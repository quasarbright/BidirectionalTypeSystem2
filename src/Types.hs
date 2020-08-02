module Types where

import Common
import qualified Data.Set as Set
import Data.List

data Type a = One a
          | TInt a
          | UVar String a
          | EVar String a
          | TyScheme String (Type a) a
          | TyArr (Type a) (Type a) a
          | TyTup [Type a] a

instance Show (Type a) where
  showsPrec p t =
      let p' = getPrecedence t in
      case t of
        One _ -> showString "1"
        TInt _ -> showString "Int"
        UVar name _ -> shows (UName name)
        EVar name _ -> shows (EName name)
        TyScheme name body _ -> showParen (p > p') $ showString "\\/" . shows (UName name) . showString "." . showsPrec p' body
        TyArr arg ret _ -> showParen (p > p') $ showsPrec (p'+1) arg . showString " -> " . showsPrec p' ret
        TyTup tys _ -> showParen True . showString . intercalate ", " $ show <$> tys

instance Eq (Type a) where
  One{} == One{} = True
  One{} == _ = False
  TInt{} == TInt{} = True
  TInt{} == _ = False
  UVar name _ == UVar name' _ = name == name'
  UVar{} == _ = False
  EVar name _ == EVar name' _ = name == name'
  EVar{} == _ = False
  TyScheme a t _ == TyScheme a' t' _ = a == a' && t == t'
  TyScheme{} == _ = False
  TyArr arg ret _ == TyArr arg' ret' _ = arg == arg' && ret == ret'
  TyArr{} == _ = False
  TyTup tys _ == TyTup tys' _ = tys == tys'
  TyTup{} == _ = False

instance Functor Type where
  fmap f (One a) = One (f a)
  fmap f (TInt a) = TInt (f a)
  fmap f (UVar name a) = UVar name (f a)
  fmap f (EVar name a) = EVar name (f a)
  fmap f (TyScheme name t a) = TyScheme name (fmap f t) (f a)
  fmap f (TyArr inTy retTy a) = TyArr (fmap f inTy) (fmap f retTy) (f a)
  fmap f (TyTup tys a) = TyTup (fmap f <$> tys) (f a)

instance Tagged Type where
  getTag (One a) = a
  getTag (TInt a) = a
  getTag (UVar _ a) = a
  getTag (EVar _ a) = a
  getTag (TyScheme _ _ a) = a
  getTag (TyArr _ _ a) = a
  getTag (TyTup _ a) = a

  setTag a (One _) = One a
  setTag a (TInt _) = TInt a
  setTag a (UVar name _) = UVar name a
  setTag a (EVar name _) = EVar name a
  setTag a (TyScheme name t _) = TyScheme name t a
  setTag a (TyArr inTy retTy _) = TyArr inTy retTy a
  setTag a (TyTup tys _) = TyTup tys a

instance ExprLike Type where
  getFreeVars One{} = Set.empty
  getFreeVars TInt{} = Set.empty
  getFreeVars (UVar name _) = Set.singleton (UName name)
  getFreeVars (EVar name _) = Set.singleton (EName name)
  getFreeVars (TyScheme name t _) = Set.delete (UName name) (getFreeVars t)
  getFreeVars (TyArr i r _) = Set.union (getFreeVars i) (getFreeVars r)
  getFreeVars (TyTup tys _) = Set.unions (getFreeVars <$> tys)

  getPrecedence One{} = 100
  getPrecedence TInt{} = 100
  getPrecedence UVar{} = 100
  getPrecedence EVar{} = 100
  getPrecedence TyScheme{} = 2
  getPrecedence TyArr{} = 3
  getPrecedence TyTup{} = 100


-- utility functions for types


-- | is the given type a mono-type? (monomorphic)
isMonoType :: Type a -> Bool
isMonoType t = case t of
  One{} -> True
  TInt{} -> True
  UVar{} -> True
  EVar{} -> True
  TyScheme{} -> False
  TyArr arg ret _ -> all isMonoType [arg, ret]
  TyTup tys _ -> all isMonoType tys

-- | @substituteTypeVariable name value t@ substitutes all references to the given name with the type @value@ in the type @t@
substituteTypeVariable :: Name -> Type a -> Type a -> Type a
substituteTypeVariable name value t =
  let recurse = substituteTypeVariable name value in
  case t of
    One{} -> t
    TInt{} -> t
    UVar name' _
      | UName name' == name -> value
      | otherwise -> t
    EVar name' _
      | EName name' == name -> value
      | otherwise -> t
    TyScheme name' body a
      | UName name' == name -> t -- shouldn't even be possible, TODO maybe throw an error?
      | otherwise -> TyScheme name' (recurse body) a
    TyArr arg ret a -> TyArr (recurse arg) (recurse ret) a
    TyTup tys a -> TyTup (recurse <$> tys) a


-- combinators for constructing types


-- | construct a unit type
one :: Type ()
one = One ()

-- | construct an integer type
tint :: Type ()
tint = TInt ()

-- | construct a variable (universal) type
uvar :: String -> Type ()
uvar name = UVar name ()

-- | construct a variable (existential) type
evar :: String -> Type ()
evar name = EVar name ()

-- | combinator for constructing type schemes
infixr 2 \/.
(\/.) :: String -> Type () -> Type ()
name \/. t = TyScheme name t ()

-- | combinator for constructing function types
infixr 3 \->
(\->) :: Type () -> Type () -> Type ()
arg \-> ret = TyArr arg ret ()

-- | combinator for constructing tuple types
ttup :: [Type ()] -> Type ()
ttup tys = TyTup tys ()

-- example: the type of the identity function
_ = "a" \/. uvar "a" \-> uvar "a"
