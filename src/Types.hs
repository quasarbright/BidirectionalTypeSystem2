module Types where

import Common
import qualified Data.Set as Set
type TyVarName = String

data Type a = One a
          | TyVar TyVarName a
          | TyScheme TyVarName (Type a) a
          | TyArr (Type a) (Type a) a
          deriving(Eq, Ord)

instance Show (Type a) where
  showsPrec p t =
      let p' = getPrecedence t in
      case t of
        One _ -> showString "1"
        TyVar name _ -> showString name
        TyScheme name body _ -> showParen (p > p') $ showString "\\/" . showString name . showString "." . showsPrec p' body
        TyArr arg ret _ -> showParen (p > p') $ showsPrec (p'+1) arg . showString " -> " . showsPrec p' ret

instance Functor Type where
  fmap f (One a) = One (f a)
  fmap f (TyVar name a) = TyVar name (f a)
  fmap f (TyScheme name t a) = TyScheme name (fmap f t) (f a)
  fmap f (TyArr inTy retTy a) = TyArr (fmap f inTy) (fmap f retTy) (f a)

instance Tagged Type where
  getTag (One a) = a
  getTag (TyVar _ a) = a
  getTag (TyScheme _ _ a) = a
  getTag (TyArr _ _ a) = a

  setTag a (One _) = One a
  setTag a (TyVar name _) = TyVar name a
  setTag a (TyScheme name t _) = TyScheme name t a
  setTag a (TyArr inTy retTy _) = TyArr inTy retTy a

instance ExprLike Type where
  getFreeVars One{} = Set.empty
  getFreeVars (TyVar name _) = Set.singleton name
  getFreeVars (TyScheme name t _) = Set.delete name (getFreeVars t)
  getFreeVars (TyArr i r _) = Set.union (getFreeVars i) (getFreeVars r)

  getPrecedence One{} = 100
  getPrecedence TyVar{} = 100
  getPrecedence TyScheme{} = 2
  getPrecedence TyArr{} = 3

-- combinators for constructing types

-- | construct a unit type
one :: Type ()
one = One ()

-- | construct a variable type
tvar :: TyVarName -> Type ()
tvar name = TyVar name ()

-- | combinator for constructing type schemes
infixr 2 \/.
(\/.) :: TyVarName -> Type () -> Type ()
name \/. t = TyScheme name t ()

-- | combinator for constructing function types
infixr 3 \->
(\->) :: Type () -> Type () -> Type ()
arg \-> ret = TyArr arg ret ()
