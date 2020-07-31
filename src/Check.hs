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
-- A TCFailure HAS A TypeError
data TypeError a = TypeWFError (ContextWFError a)
                 | ContextItemNotFound (ContextItem a)
                 | Mismatch (Type a) (Type a)
                 | AppliedNonFunction (Type a)
                 | OccursError Name (Type a)
                 | InternalCheckingError String
                 deriving(Eq, Show)

-- | Reason for an error. Or what was going on leading up to an error
-- To be maintained like a stack, pushing at the start of a computation, popping at the end.
data Reason a = Checking (Expr a) (Type a)
              | Synthesizing (Expr a)
              | ApplicationSynthesizing (Type a) (Expr a)
              | Subtyping (Type a) (Type a)
              | LeftInstantiating String (Type a)
              | RightInstantiating (Type a) String
              deriving(Eq, Show)

-- | State for the type checker. Contains the type context, the current expression being typed, and the reasons the type checker
-- is doing what it's doing (most recent first).
-- The current expression and reasons are initialized when running the computation. All typing functions assume that the current expression
-- and reasons are up to date upon invocation, but they are responsible for temporarily updating when typing
-- subexpressions. For example, when type checking a lambda, it is assumed that the current expression is the lambda.
-- But when the body is checked, the current expression must temporarily be set to the body expression and a checking reason must be temporarily pushed.
data TCState a = TCState { stateContext :: Context a, stateExpr :: Maybe (Expr a), stateReasons :: [Reason a] } deriving(Eq, Show)


-- | Empty type checking state
emptyState :: TCState a
emptyState = TCState{stateContext = emptyContext, stateExpr = Nothing, stateReasons = []}

-- | Make a type checking state from the given context.
makeState :: Context a -> TCState a
makeState ctx = emptyState{stateContext = ctx}

-- | Type alias used in signatures of runner functions to encapsulate the type
type TCMonad a = (Either (TypeError a, TCState a))

-- | Monad stack for type checking. Holds a context as state and operates on Either type errors or b's
type TypeChecker a b = StateT (TCState a) (TCMonad a) b

-- | Initial context for type checking. Contains builtins and their types.
initialContext :: Context a
initialContext = emptyContext


-- utilities


-- | utility for throwing type errors in a @TypeChecker@ do block
throw :: TypeError a -> TypeChecker a b
throw err = do
  s <- get
  lift (Left (err, s))

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
getContext = stateContext <$> get

-- | get the current expression being typed
getCurrentExpr :: TypeChecker a (Maybe (Expr a))
getCurrentExpr = stateExpr <$> get

getReasons :: TypeChecker a [Reason a]
getReasons = stateReasons <$> get

-- | set the context of the type checker
putContext :: Context a -> TypeChecker a ()
putContext ctx = do
  s <- get
  put s{stateContext=ctx}

-- | set the current expression being typed
putCurrentExpr :: Expr a -> TypeChecker a ()
putCurrentExpr e = do
  s <- get
  put s{stateExpr=Just e}

-- | set the current list of reasons we're here
putReasons :: [Reason a] -> TypeChecker a ()
putReasons reasons = do
  s <- get
  put s{stateReasons=reasons}

-- | locally set the current expression being typed in the given computation, and restore it to its previous value upon
-- successful completion of the computation.
localExpr :: Expr a -> TypeChecker a b -> TypeChecker a b
localExpr e tc = do
  old <- getCurrentExpr
  putCurrentExpr e
  result <- tc
  s <- get
  case old of
    Just oldExpr -> putCurrentExpr oldExpr
    Nothing -> put s{stateExpr=Nothing}
  return result

-- | locally push a reason for the given computation and restore the old reason list upon successful completion of the
-- computation.
localReason :: Reason a -> TypeChecker a b -> TypeChecker a b
localReason reason tc = do
  oldReasons <- getReasons
  putReasons (reason:oldReasons)
  result <- tc
  putReasons oldReasons
  return result

-- | locally set the current expr and push a reason, restoring after the computation succeeds
localReasonExpr :: Reason a -> Expr a -> TypeChecker a b -> TypeChecker a b
localReasonExpr reason expr = localReason reason . localExpr expr

-- | modify the context of the type checker
modifyContextTC :: (Context a -> Context a) -> TypeChecker a ()
modifyContextTC f = modify $ \s -> s{stateContext = f (stateContext s)}

-- | simplify a type with respect to the current context (replaces existentials with their solutions).
simplify :: Type a -> TypeChecker a (Type a)
simplify t = do
  simplifier <- contextAsSubstitution <$> getContext
  return (simplifier t)

-- subtyping and instantiation

-- | wrapper for \<: that adds handles logging. Only use this one
infix 4 <:
(<:) :: Type a -> Type a -> TypeChecker a ()
t1 <: t2 = localReason (Subtyping t1 t2) $ t1 \<: t2

-- | @A \<: B@ asserts that A is a subtype of B, where subtype means "more polymorphic than".
-- May modify context to make the assertion be valid, such as the case of a? \<: A.
infix 4 \<:
(\<:) :: Type a -> Type a -> TypeChecker a ()
-- Exvar
EVar name _ \<: EVar name' _
  -- don't mismatch if names are different. InstantiateL will handle that
  | name == name' = assertCtxHasEDecl name
-- Var
UVar name tag \<: UVar name' tag' = do
  assertTypeWF (UVar name tag)
  assertTypeWF (UVar name' tag')
  unless (name == name') (mismatch (UVar name tag) (UVar name' tag'))
-- Unit
One{} \<: One{} = return ()
TInt{} \<: TInt{} = return ()
-- ->
TyArr arg ret _ \<: TyArr arg' ret' _ = do
  arg' <: arg
  retSimplified <- simplify ret
  ret'Simplified <- simplify ret'
  retSimplified <: ret'Simplified
-- forall L
TyScheme name body tag \<: t = do
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
t \<: TyScheme name body _ = do
  modifyContextTC $ addUDecl name
  t <: body
  modifyContextTC $ removeItemsAfterUDecl name
-- InstantiateL
EVar name _ \<: t = do
  assertCtxHasEDecl name
  occursCheck (EName name) t
  instantiateL name t
-- InstantiateR
t \<: EVar name _ = do
  assertCtxHasEDecl name
  occursCheck (EName name) t
  instantiateR t name
-- These need to be last so they don't cover the scheme cases
a@UVar{} \<: b = mismatch a b
a@One{} \<: b = mismatch a b
a@TInt{} \<: b = mismatch a b
a@TyArr{} \<: b = mismatch a b

-- | run the subtype assertion with the given initial context, ignoring the final context
evalSubtype :: Type a -> Type a -> Context a -> TCMonad a ()
evalSubtype a b ctx = evalStateT (a \<: b) (TCState{stateContext=ctx, stateExpr=Nothing, stateReasons=[Subtyping a b]})

-- | run the subtype assertion with the given initial context, returning the final context
runSubtype :: Type a -> Type a -> Context a -> TCMonad a (TCState a)
runSubtype a b ctx  = snd <$> runStateT (a <: b) (TCState{stateContext=ctx, stateExpr=Nothing, stateReasons=[Subtyping a b]})

-- | wrapper for _instantiateL that handles logging. Only call this one
instantiateL :: String -> Type a -> TypeChecker a ()
instantiateL eName t = localReason (LeftInstantiating eName t) (_instantiateL eName t)

-- | Instantiate the specified existential such that a? <: A (subtype).
-- May modify context
_instantiateL :: String -> Type a -> TypeChecker a ()
-- InstLReach (and the case of InstLSolve where tau is an existential b? declared before a? s.t. Gamma[b?][a?])
_instantiateL name (EVar name' tag') = reachHelp name name' tag'
-- InstLArr
_instantiateL name (TyArr argType retType tag) = do
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
_instantiateL name (TyScheme uname body _) = do
  assertCtxHasEDecl name
  modifyContextTC $ addUDecl uname
  _instantiateL name body
  modifyContextTC $ removeItemsAfterUDecl uname
-- InstLSolve
_instantiateL name t = do
  assertCtxHasEDecl name
  assertTypeWF t
  modifyContextTC $ recordESol name t

-- | wrapper for _instantiateR that handles logging. Only use this one
instantiateR :: Type a -> String -> TypeChecker a ()
instantiateR t eName = localReason (RightInstantiating t eName) (_instantiateR t eName)

-- | Instantiate the specified existential such that A <: a? (supertype).
-- May modify context
_instantiateR :: Type a -> String -> TypeChecker a ()
-- InstRReach (and the case of InstRSolve where tau is an existential b? declared before a? s.t. Gamma[b?][a?])
_instantiateR (EVar name tag) name' = reachHelp name name' tag
-- InstRArr
_instantiateR (TyArr argType retType tag) name = do
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
_instantiateR (TyScheme uName body tag) name = do
  assertCtxHasEDecl name
  (eName, ctxAfterName) <- getFreshNameFrom uName <$> getContext
  putContext ctxAfterName
  modifyContextTC $ addEMarker eName
  modifyContextTC $ addEDecl eName
  let bodyWithExistential = substituteTypeVariable (UName uName) (EVar eName tag) body
  instantiateR bodyWithExistential name
  modifyContextTC $ removeItemsAfterEMarker eName
-- InstRSolve
_instantiateR t name = do
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
  case whichEDeclLast name name' ctx of
    Nothing -> error ("at least one edecl unbound of: "++show (EName name)++" and "++show (EName name'))
    Just lastName
      -- Gamma[name][name'] -> Gamma[name][name' = name] (? omitted for easy reading)
      | lastName == name' -> modifyContextTC $ recordESol name' (EVar name tag)
      -- Gamma[name'][name] -> Gamma[name'][name = name'] (? omitted for easy reading)
      | otherwise -> modifyContextTC $ recordESol name (EVar name' tag)


-- checking and inference

-- | wrapper for typeCheck that handles logging. Only use this one.
typeCheck :: Expr a -> Type a -> TypeChecker a ()
typeCheck e t = localReasonExpr (Checking e t) e (_typeCheck e t)

-- | Check that the expression is a subtype of the given type
_typeCheck :: Expr a -> Type a -> TypeChecker a ()
-- 1I<=
_typeCheck Unit{} One{} = return ()
-- IntI<=
_typeCheck EInt{} TInt{} = return ()
-- \/I <=
_typeCheck e (TyScheme uName body _) = do
  modifyContextTC $ addUDecl uName
  typeCheck e body
  modifyContextTC $ removeItemsAfterUDecl uName
-- ->I <=
_typeCheck (Lambda name body _) (TyArr argType retType _) = do
  modifyContextTC $ addVarAnnot name argType
  typeCheck body retType
  modifyContextTC $ removeItemsAfterVarAnnot name argType
_typeCheck (LambdaAnnot name t body tag) arr@(TyArr argType retType tag') = do
  TyArr t retType tag' <: TyArr argType retType tag'
  _typeCheck (Lambda name body tag) arr
-- TODO tuple checking here similar to ->I <=
-- Sub
_typeCheck e expectedType = do
  synthesizedType <- typeSynth e
  synthesizedType' <-  simplify synthesizedType
  expectedType' <- simplify expectedType
  synthesizedType' <: expectedType'

-- | Type check with the given context
runTypeCheck :: Expr a -> Type a -> Context a -> TCMonad a (TCState a)
runTypeCheck e t ctx = snd <$> runStateT (_typeCheck e t) (TCState{stateContext = ctx, stateExpr = Just e, stateReasons = [Checking e t]})

-- | wrapper for _typeSynth that handles logging. Only use this one
typeSynth :: Expr a -> TypeChecker a (Type a)
typeSynth e = localReasonExpr (Synthesizing e) e (_typeSynth e)

-- | Synthesize a type for the given expression
_typeSynth :: Expr a -> TypeChecker a (Type a)
-- Var
_typeSynth (Var name _) = do
  ctx <- getContext
  case lookupVar name ctx of
    Just t -> return t
    _ -> error "unbound variable in type synthesis"
-- Anno
_typeSynth (Annot e t _) = do
  typeCheck e t
  return t
-- 1I =>
_typeSynth (Unit tag) = return $ One tag
-- IntI =>
_typeSynth (EInt _ tag) = return $ TInt tag
-- ->I =>
_typeSynth (Lambda name body tag) = do
  (argName, ctx') <- getFreshNameFrom "a" <$> getContext
  let (retName, ctx'') = getFreshNameFrom "b" ctx'
  putContext ctx''
  let argType = EVar argName tag
  let retType = EVar retName tag
  modifyContextTC $ addEDecl argName
  typeSynthLambdaHelp name retName argType retType body tag
-- ->AnnotI =>
-- instead of \x.e => a? -> b?, it's \x::A.e => A -> b?
_typeSynth (LambdaAnnot name t body tag) = do
  (retName, ctx') <- getFreshNameFrom "b" <$> getContext
  putContext ctx'
  let argType = t
  let retType = EVar retName tag
  typeSynthLambdaHelp name retName argType retType body tag
-- let =>
_typeSynth (Let x e body _) = do
  tX <- typeSynth e
  typeSynthLetHelp x tX body
-- letAnnot =>
_typeSynth (LetAnnot x tX e body _) = do
  typeCheck e tX
  typeSynthLetHelp x tX body
-- ->E =>
_typeSynth (App f x _) = do
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
typeSynthLetHelp :: String -> Type a -> Expr a -> TypeChecker a (Type a)
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
runTypeSynth :: Expr a -> Context a -> TCMonad a (Type a, TCState a)
runTypeSynth e ctx = runStateT (_typeSynth e) (TCState{stateContext = ctx, stateExpr = Just e, stateReasons = [Synthesizing e]})

-- | Run type synthesis under the given context and simplify the result type
runTypeSynthSimplify :: Expr a -> Context a -> TCMonad a (Type a, TCState a)
runTypeSynthSimplify e ctx = runStateT res (TCState{stateContext = ctx, stateExpr = Just e, stateReasons = [Synthesizing e]})
  where
    res = do
      t <- _typeSynth e
      simplify t

-- | wrapper for _typeSynthApp that handles logging
typeSynthApp :: Type a -> Expr a -> TypeChecker a (Type a)
typeSynthApp fT x = localReason (ApplicationSynthesizing fT x) (_typeSynthApp fT x)

-- | Given a function type and argument expression being applied to a function of that type,
-- synthesize the type of the application.
_typeSynthApp :: Type a -> Expr a -> TypeChecker a (Type a)
-- \/ app
_typeSynthApp (TyScheme uName body tag) x = do
  (eName, ctxAfterName) <- getFreshNameFrom uName <$> getContext
  putContext ctxAfterName
  let eType = EVar eName tag
  modifyContextTC $ addEDecl eName
  let eBody = substituteTypeVariable (UName uName) eType body
  typeSynthApp eBody x
-- ->App
_typeSynthApp (TyArr argType retType _) x = do
  typeCheck x argType
  return retType
-- a?App
_typeSynthApp (EVar eName tag) x = do
  assertCtxHasItem (EDecl eName)
  (argName, retName, ctx') <- instArrReplacement eName tag <$> getContext
  putContext ctx'
  let argType = EVar argName tag
  let retType = EVar retName tag
  typeCheck x argType
  return retType
-- tried to apply non-function type. Mismatch
_typeSynthApp t _ = throw $ AppliedNonFunction t
