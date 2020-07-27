module Check where

import Control.Monad.Trans.State.Strict
import Common
--import Exprs
import Types
import Environment
import Control.Monad.Trans.Class (lift)
import Control.Monad

-- TODO add location, maybe exprs/reasons
-- | Type error.
data TypeError a = TypeWFError (ContextWFError a)
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


-- subtyping and instantiation

-- TODO assert decls in context for Gamma[a]
-- TODO should you try foralls first, or instantiates first? going with vertical order in the paper for now.
-- | A <: B asserts that A is a subtype of B, where subtype means "more polymorphic than".
-- May modify context to make the assertion be valid, such as the case of a? <: A.
infix 4 <:
(<:) :: Type a -> Type a -> TypeChecker a ()
-- Exvar
EVar name _ <: EVar name' _
  -- don't mismatch if names are different. InstantiateL will handle that
  | name == name' = return ()
-- Var
UVar name tag <: UVar name' tag' = unless (name == name') (throw (Mismatch (UVar name tag) (UVar name' tag')))
-- Unit
One{} <: One{} = return ()
-- ->
TyArr arg ret _ <: TyArr arg' ret' _ = do
  arg' <: arg
  -- output context of arg' <: arg
  ctx' <- getContext
  let substitute = contextAsSubstitution ctx'
  substitute ret <: substitute ret'
-- forall L
TyScheme name body tag <: t = do
  startCtx <- getContext
  let (eName, startCtx') = getFreshNameFrom name startCtx
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
  startCtx <- getContext
  let ctxWithADecl = startCtx |> addUDecl name
  put ctxWithADecl
  t <: body
  modifyContextTC $ removeItemsAfterUDecl name
-- InstantiateL
EVar name _ <: t = do
  occursCheck (EName name) t
  instantiateL name t
-- InstantiateR
t <: EVar name _ = do
  occursCheck (EName name) t
  instantiateR t name
-- These need to be last so they don't cover the scheme cases
a@UVar{} <: b = throw (Mismatch a b)
a@One{} <: b = throw (Mismatch a b)
a@TyArr{} <: b = throw (Mismatch a b)

-- | run the subtype assertion with the given initial context
runSubtype :: Type a -> Type a -> Context a -> Either (TypeError a) ()
runSubtype a b = evalStateT (a <: b)

-- | Instantiate the specified existential such that a? <: A (subtype).
-- May modify context
instantiateL :: String -> Type a -> TypeChecker a ()
instantiateL = undefined

-- | Instantiate the specified existential such that A <: a? (supertype).
-- May modify context
instantiateR :: Type a -> String -> TypeChecker a ()
instantiateR = undefined

-- | Check that the given name does not occur free in the given type. Used to detect infinite types like a = 1 -> a.
occursCheck :: Name -> Type a -> TypeChecker a ()
occursCheck name t = when (name `elem` getFreeVars t) (throw (OccursError name t))

-- checking and inference