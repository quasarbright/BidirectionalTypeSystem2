module Check where

import Control.Monad.Trans.State.Strict
import Common
import Exprs
import Types
import Environment
import Control.Monad.Trans.Class (lift)
import Control.Monad

-- TODO add location, maybe exprs/reasons
-- | Type error.
data TypeError a = TypeWFError (ContextWFError a)
                 | ContextItemNotFound (ContextItem a)
                 | Mismatch (Type a) (Type a)
                 | OccursError Name (Type a)
                 | InternalCheckingError String
                 deriving(Eq, Show)

-- TODO add a current location to the state for error location, and maybe exprs/reasons
-- | Monad stack for type checking. Holds a context as state and operates on Either type errors or b's
type TypeChecker a b = StateT (Context a) (Either (TypeError a)) b

-- | Initial context for type checking. Contains builtins and their types.
initialContext :: Context a
initialContext = emptyContext


-- utilities


-- | utility for throwing type errors in a @TypeChecker@ do block
throw :: TypeError a -> TypeChecker a b
throw = lift . Left

-- | throw a mismatch error with the two types simplified
mismatch :: Type a -> Type a -> TypeChecker a b
mismatch a b = do
  a' <- simplify a
  b' <- simplify b
  throw $ Mismatch a' b'

-- | Assert that the current context is well-formed
assertCtxWF :: TypeChecker a ()
assertCtxWF = do
  ctx <- getContext
  case checkContextWellFormedness ctx of
    Left err -> throw $ TypeWFError err
    Right () -> return ()

-- | Assert that the current type is well-formed
assertTypeWF :: Type a -> TypeChecker a ()
assertTypeWF t = do
  ctx <- getContext
  case checkTypeWellFormedness ctx t of
    Left err -> throw $ TypeWFError err
    Right () -> return ()

-- | Assert that the current context contains an e decl of the specified name
assertCtxHasEDecl :: String -> TypeChecker a ()
assertCtxHasEDecl = assertCtxHasItem . EDecl

-- | Assert that the current context contains the given context item (e sol not ok)
assertCtxHasItem :: ContextItem a -> TypeChecker a ()
assertCtxHasItem item = do
  ctx <- getContext
  case findItem (==item) ctx of
    Just{} -> return ()
    Nothing -> throw $ ContextItemNotFound item

-- I'm making these functions now in case I eventually add more than just a context to the state.
-- That way, I won't have to change how existing code is written, just these functions

-- | get the context of the type checker
getContext :: TypeChecker a (Context a)
getContext = get

-- | set the context of the type checker
putContext :: Context a -> TypeChecker a ()
putContext = put

-- | modify the context of the type checker
modifyContextTC :: (Context a -> Context a) -> TypeChecker a ()
modifyContextTC = modify

simplify :: Type a -> TypeChecker a (Type a)
simplify t = do
  simplifier <- contextAsSubstitution <$> getContext
  return (simplifier t)

-- subtyping and instantiation

-- TODO assert decls in context for Gamma[a]
-- | A <: B asserts that A is a subtype of B, where subtype means "more polymorphic than".
-- May modify context to make the assertion be valid, such as the case of a? <: A.
infix 4 <:
(<:) :: Type a -> Type a -> TypeChecker a ()
-- Exvar
EVar name _ <: EVar name' _
  -- don't mismatch if names are different. InstantiateL will handle that
  | name == name' = assertCtxHasEDecl name
-- Var
UVar name tag <: UVar name' tag' = do
  assertTypeWF (UVar name tag)
  assertTypeWF (UVar name' tag')
  unless (name == name') (mismatch (UVar name tag) (UVar name' tag'))
-- Unit
One{} <: One{} = return ()
TInt{} <: TInt{} = return ()
-- ->
TyArr arg ret _ <: TyArr arg' ret' _ = do
  arg' <: arg
  retSimplified <- simplify ret
  ret'Simplified <- simplify ret'
  retSimplified <: ret'Simplified
-- forall L
TyScheme name body tag <: t = do
  (eName, startCtx') <- getFreshNameFrom name <$> getContext
  let markedCtx = startCtx'
                  |> addEMarker eName
                  |> addEDecl eName
  putContext markedCtx
  let eBody = substituteTypeVariable (UName name) (EVar eName tag) body
  eBody <: t
  modifyContextTC $ removeItemsAfterEMarker eName
-- no need for a@TyScheme{} <: b, it's already covered
-- forall R
t <: TyScheme name body _ = do
  modifyContextTC $ addUDecl name
  t <: body
  modifyContextTC $ removeItemsAfterUDecl name
-- InstantiateL
EVar name _ <: t = do
  assertCtxHasEDecl name
  occursCheck (EName name) t
  instantiateL name t
-- InstantiateR
t <: EVar name _ = do
  assertCtxHasEDecl name
  occursCheck (EName name) t
  instantiateR t name
-- These need to be last so they don't cover the scheme cases
a@UVar{} <: b = mismatch a b
a@One{} <: b = mismatch a b
a@TInt{} <: b = mismatch a b
a@TyArr{} <: b = mismatch a b

-- | run the subtype assertion with the given initial context, ignoring the final context
evalSubtype :: Type a -> Type a -> Context a -> Either (TypeError a) ()
evalSubtype a b = evalStateT (a <: b)

-- | run the subtype assertion with the given initial context, returning the final context
runSubtype :: Type a -> Type a -> Context a -> Either (TypeError a) (Context a)
runSubtype a b ctx  = snd <$> runStateT (a <: b) ctx

-- | Instantiate the specified existential such that a? <: A (subtype).
-- May modify context
instantiateL :: String -> Type a -> TypeChecker a ()
-- InstLReach (and the case of InstLSolve where tau is an existential b? declared before a? s.t. Gamma[b?][a?])
instantiateL name (EVar name' tag') = reachHelp name name' tag'
-- InstLArr
instantiateL name (TyArr argType retType tag) = do
  assertCtxHasEDecl name
  -- argName and retName are the names of the existentials corresponding to argType and retType
  (argName, retName, articulatedCtx) <- instArrReplacement name tag <$> getContext
  putContext articulatedCtx
  -- we need to take in argType or more, so we need the supertype
  instantiateR argType argName
  simplifiedRetType <- simplify retType
  -- we need to return retType or less, so we need the subtype
  instantiateL retName simplifiedRetType
-- InstLAllR
instantiateL name (TyScheme uname body _) = do
  assertCtxHasEDecl name
  modifyContextTC $ addUDecl uname
  instantiateL name body
  modifyContextTC $ removeItemsAfterUDecl uname
-- InstLSolve
instantiateL name t = do
  assertCtxHasEDecl name
  assertTypeWF t
  modifyContextTC $ recordESol name t

-- | Instantiate the specified existential such that A <: a? (supertype).
-- May modify context
instantiateR :: Type a -> String -> TypeChecker a ()
-- InstRReach (and the case of InstRSolve where tau is an existential b? declared before a? s.t. Gamma[b?][a?])
instantiateR (EVar name tag) name' = reachHelp name name' tag
-- InstRArr
instantiateR (TyArr argType retType tag) name = do
  -- TODO abstract with instantiateLArr
  assertCtxHasEDecl name
  -- argName and retName are the names of the existentials corresponding to argType and retType
  (argName, retName, articulatedCtx) <- instArrReplacement name tag <$> getContext
  putContext articulatedCtx
  -- we need to take in argType or less, so subtype
  instantiateL argName argType
  simplifiedRetType <- simplify retType
  -- we need to return retType or more, so supertype
  instantiateR simplifiedRetType retName
-- InstRAllL
instantiateR (TyScheme uName body tag) name = do
  assertCtxHasEDecl name
  (eName, ctxAfterName) <- getFreshNameFrom uName <$> getContext
  putContext ctxAfterName
  modifyContextTC $ addEMarker eName
  modifyContextTC $ addEDecl eName
  let bodyWithExistential = substituteTypeVariable (UName uName) (EVar eName tag) body
  instantiateR bodyWithExistential name
  modifyContextTC $ removeItemsAfterEMarker eName
-- InstRSolve
instantiateR t name = do
  assertCtxHasEDecl name
  assertTypeWF t
  modifyContextTC $ recordESol name t


-- | Check that the given name does not occur free in the given type. Used to detect infinite types like a = 1 -> a.
occursCheck :: Name -> Type a -> TypeChecker a ()
occursCheck name t = when (name `elem` getFreeVars t) (throw (OccursError name t))

-- | given two existential names, set them equal to each other
-- while preserving context well-formedness
reachHelp :: String -> String -> a -> TypeChecker a ()
reachHelp name name' tag = do
  assertCtxHasEDecl name
  assertCtxHasEDecl name'
  ctx <- getContext
  -- TODO check both types' well-formedness with respect to ctx
  case whichEDeclLast name name' ctx of
    Nothing -> error ("at least one edecl unbound of: "++show (EName name)++" and "++show (EName name'))
    Just lastName
      -- Gamma[name][name'] -> Gamma[name][name' = name] (? omitted for easy reading)
      | lastName == name' -> modifyContextTC $ recordESol name' (EVar name tag)
      -- Gamma[name'][name] -> Gamma[name'][name = name'] (? omitted for easy reading)
      | otherwise -> modifyContextTC $ recordESol name (EVar name' tag)


-- checking and inference


-- | Check that the expression is a subtype of the given type
typeCheck :: Expr a -> Type a -> TypeChecker a ()
-- 1I<=
typeCheck Unit{} One{} = return ()
-- IntI<=
typeCheck EInt{} TInt{} = return ()
-- \/I <=
typeCheck e (TyScheme uName body _) = do
  modifyContextTC $ addUDecl uName
  typeCheck e body
  modifyContextTC $ removeItemsAfterUDecl uName
-- ->I <=
typeCheck (Lambda name body _) (TyArr argType retType _) = do
  modifyContextTC $ addVarAnnot name argType
  typeCheck body retType
  modifyContextTC $ removeItemsAfterVarAnnot name argType
typeCheck (LambdaAnnot name t body tag) arr@(TyArr argType retType tag') = do
  TyArr t retType tag' <: TyArr argType retType tag'
  typeCheck (Lambda name body tag) arr
-- TODO tuple checking here similar to ->I <=
-- Sub
typeCheck e expectedType = do
  synthesizedType <- typeSynth e
  synthesizedType' <-  simplify synthesizedType
  expectedType' <- simplify expectedType
  synthesizedType' <: expectedType'

-- | Type check with the given context
runTypeCheck :: Expr a -> Type a -> Context a -> Either (TypeError a) (Context a)
runTypeCheck e t ctx = snd <$> runStateT (typeCheck e t) ctx

-- | Synthesize a type for the given expression
typeSynth :: Expr a -> TypeChecker a (Type a)
-- Var
typeSynth (Var name _) = do
  ctx <- getContext
  case lookupVar name ctx of
    Just t -> return t
    _ -> error "unbound variable in type synthesis"
-- Anno
typeSynth (Annot e t _) = do
  typeCheck e t
  return t
-- 1I =>
typeSynth (Unit tag) = return $ One tag
-- IntI =>
typeSynth (EInt _ tag) = return $ TInt tag
-- ->I =>
typeSynth (Lambda name body tag) = do
  (argName, ctx') <- getFreshNameFrom "a" <$> getContext
  let (retName, ctx'') = getFreshNameFrom "b" ctx'
  putContext ctx''
  let argType = EVar argName tag
  let retType = EVar retName tag
  modifyContextTC $ addEDecl argName
  typeSynthLambdaHelp name retName argType retType body tag
-- ->AnnotI =>
-- instead of \x.e => a? -> b?, it's \x::A.e => A -> b?
typeSynth (LambdaAnnot name t body tag) = do
  (retName, ctx') <- getFreshNameFrom "b" <$> getContext
  putContext ctx'
  let argType = t
  let retType = EVar retName tag
  typeSynthLambdaHelp name retName argType retType body tag
-- let =>
typeSynth (Let x e body _) = do
  tX <- typeSynth e
  typeSynthLetHelp x tX body
-- letAnnot =>
typeSynth (LetAnnot x tX e body _) = do
  typeCheck e tX
  typeSynthLetHelp x tX body
-- ->E =>
typeSynth (App f x _) = do
  fType <- typeSynth f
  fType' <- simplify fType
  typeSynthApp fType' x

-- | common bit between lambda and lambda annot synthesis cases with free variables extracted as parameters.
typeSynthLambdaHelp :: String -> String -> Type a -> Type a -> Expr a -> a -> TypeChecker a (Type a)
typeSynthLambdaHelp name retName argType retType body tag = do
  modifyContextTC $ addEDecl retName
  modifyContextTC $ addVarAnnot name argType
  typeCheck body retType
  modifyContextTC $ removeItemsAfterVarAnnot name argType
  return $ TyArr argType retType tag

-- | common bit between let and letAnnot synthesis cases with free variables extracted as parameters
-- uses the same trick as the ->I => rule for keeping the output existential and eliminating anything after the x::A
-- in the output context
typeSynthLetHelp :: String -> Type a -> Expr a -> StateT (Context a) (Either (TypeError a)) (Type a)
typeSynthLetHelp x tX body = do
  (tBodyName, ctx') <- getFreshNameFrom "b" <$> getContext
  putContext ctx'
  modifyContextTC $ addEDecl tBodyName
  modifyContextTC $ addVarAnnot x tX
  let tBody = EVar tBodyName (getTag body)
  typeCheck body tBody
  modifyContextTC $ removeItemsAfterVarAnnot x tX
  return tBody

-- | Run type synthesis under the given context
runTypeSynth :: Expr a -> Context a -> Either (TypeError a) (Type a, Context a)
runTypeSynth e = runStateT (typeSynth e)

-- | Run type synthesis under the given context and simplify the result type
runTypeSynthSimplify :: Expr a -> Context a -> Either (TypeError a) (Type a, Context a)
runTypeSynthSimplify e = runStateT res
  where
    res = do
      t <- typeSynth e
      simplify t

-- | Given a function type and argument expression being applied to a function of that type,
-- synthesize the type of the application.
typeSynthApp :: Type a -> Expr a -> TypeChecker a (Type a)
-- \/ app
typeSynthApp (TyScheme uName body tag) x = do
  (eName, ctxAfterName) <- getFreshNameFrom uName <$> getContext
  putContext ctxAfterName
  let eType = EVar eName tag
  modifyContextTC $ addEDecl eName
  let eBody = substituteTypeVariable (UName uName) eType body
  typeSynthApp eBody x
-- ->App
typeSynthApp (TyArr argType retType _) x = do
  typeCheck x argType
  return retType
-- a?App
typeSynthApp (EVar eName tag) x = do
  assertCtxHasItem (EDecl eName)
  (argName, retName, ctx') <- instArrReplacement eName tag <$> getContext
  putContext ctx'
  let argType = EVar argName tag
  let retType = EVar retName tag
  typeCheck x argType
  return retType
-- tried to apply non-function type. Mismatch
-- TODO maybe manually throw Mismatch here?
typeSynthApp t _ = throw $ Mismatch (TyArr (EVar "a" tag) (EVar "b" tag) tag) t
  where tag = getTag t