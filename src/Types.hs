module Types where

import Common
import qualified Data.Set as Set
import Data.List

data Type a = TInt a
            | UVar String a
            | EVar String a
            | TyScheme String (Type a) a
            | TyArr (Type a) (Type a) a
            | TyTup [Type a] a
            | TyCon String a
            | TyApp (Type a) (Type a) a

instance Show (Type a) where
  showsPrec p t =
      let p' = getPrecedence t in
      case t of
        TInt _ -> showString "Int"
        UVar name _ -> shows (UName name)
        EVar name _ -> shows (EName name)
        TyScheme name body _ -> showParen (p > p') $ showString "\\/" . shows (UName name) . showString "." . showsPrec p' body
        TyArr arg ret _ -> showParen (p > p') $ showsPrec (p'+1) arg . showString " -> " . showsPrec p' ret
        TyTup tys _ -> showParen True . showString . intercalate ", " $ show <$> tys
        TyCon name _ -> shows (DName name)
        TyApp f x _ -> showParen (p > p') $ showsPrec p' f . showString " " . showsPrec (p'+1) x

instance Eq (Type a) where
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
  TyCon name _ == TyCon name' _ = name == name'
  TyCon{} == _ = False
  TyApp f x _ == TyApp f' x' _ = (f,x) == (f',x')
  TyApp{} == _ = False

instance Functor Type where
  fmap f (TInt a) = TInt (f a)
  fmap f (UVar name a) = UVar name (f a)
  fmap f (EVar name a) = EVar name (f a)
  fmap f (TyScheme name t a) = TyScheme name (fmap f t) (f a)
  fmap f (TyArr inTy retTy a) = TyArr (fmap f inTy) (fmap f retTy) (f a)
  fmap f (TyTup tys a) = TyTup (fmap f <$> tys) (f a)
  fmap f (TyCon name a) = TyCon name (f a)
  fmap f (TyApp g x a) = TyApp (f <$> g) (f <$> x) (f a)

instance Tagged Type where
  getTag (TInt a) = a
  getTag (UVar _ a) = a
  getTag (EVar _ a) = a
  getTag (TyScheme _ _ a) = a
  getTag (TyArr _ _ a) = a
  getTag (TyTup _ a) = a
  getTag (TyCon _ a) = a
  getTag (TyApp _ _ a) = a

  setTag a (TInt _) = TInt a
  setTag a (UVar name _) = UVar name a
  setTag a (EVar name _) = EVar name a
  setTag a (TyScheme name t _) = TyScheme name t a
  setTag a (TyArr inTy retTy _) = TyArr inTy retTy a
  setTag a (TyTup tys _) = TyTup tys a
  setTag a (TyCon name _) = TyCon name a
  setTag a (TyApp f x _) = TyApp f x a

instance ExprLike Type where
  getFreeVars TInt{} = Set.empty
  getFreeVars (UVar name _) = Set.singleton (UName name)
  getFreeVars (EVar name _) = Set.singleton (EName name)
  getFreeVars (TyScheme name t _) = Set.delete (UName name) (getFreeVars t)
  getFreeVars (TyArr i r _) = Set.union (getFreeVars i) (getFreeVars r)
  getFreeVars (TyTup tys _) = Set.unions (getFreeVars <$> tys)
  getFreeVars (TyCon name _) = Set.singleton (DName name)
  getFreeVars (TyApp f x _) = Set.unions (getFreeVars <$> [f,x])

  getPrecedence TInt{} = 100
  getPrecedence UVar{} = 100
  getPrecedence EVar{} = 100
  getPrecedence TyScheme{} = 2
  getPrecedence TyArr{} = 3
  getPrecedence TyTup{} = 100
  getPrecedence TyCon{} = 100
  getPrecedence TyApp{} = 10

-- TODO full-on kind system in prep for type classes
-- want to be able to do data FunctorWrapper (f :: * -> *) a = FunctorWrapper (f a)
-- or even                    FunctorWrapper f a = FunctorWrapper (f a)
--   and have it infer the kind. This would require a lot of work though. You're going to need a set of analogous constructs
--   for kind checking like kind existentials. Or maybe you won't because it's monomorphic. think about it.
--   Eh, you'll probably want at least existentials.
data Kind a = KType a | KArr (Kind a) (Kind a) a

instance Show (Kind a) where
    showsPrec p k =
        let p' = getPrecedence k in
            case k of
                KType{} -> showString "*"
                KArr arg ret _ -> showParen (p > p') $ showsPrec (p'+1) arg . showString " -> " . showsPrec p' ret

instance Eq (Kind a) where
    KType{} == KType{} = True
    KType{} == _ = False
    KArr arg ret _ == KArr arg' ret' _ = (arg, ret) == (arg', ret')
    KArr{} == _ = False

instance Functor Kind where
    fmap f (KType a) = KType (f a)
    fmap f (KArr arg ret a) = KArr (f <$> arg) (f <$> ret) (f a)

instance Tagged Kind where
    getTag (KType a) = a
    getTag (KArr _ _ a) = a

    setTag a KType{} = KType a
    setTag a (KArr arg ret _) = KArr arg ret a

instance ExprLike Kind where
    getFreeVars _ = Set.empty

    getPrecedence KType{} = 100
    getPrecedence KArr{} = 3

-- utility functions for types


-- | is the given type a mono-type? (monomorphic)
isMonoType :: Type a -> Bool
isMonoType t = case t of
  TInt{} -> True
  UVar{} -> True
  EVar{} -> True
  TyScheme{} -> False
  TyArr arg ret _ -> all isMonoType [arg, ret]
  TyTup tys _ -> all isMonoType tys
  TyCon{} -> True
  TyApp f x _ -> all isMonoType [f, x]

-- | @substituteTypeVariable name value t@ substitutes all references to the given name with the type @value@ in the type @t@
substituteTypeVariable :: Name -> Type a -> Type a -> Type a
substituteTypeVariable name value t =
  let recurse = substituteTypeVariable name value in
  case t of
    TInt{} -> t
    UVar name' _
      | UName name' == name -> value
      | otherwise -> t
    EVar name' _
      | EName name' == name -> value
      | otherwise -> t
    TyScheme name' body a
      | UName name' == name -> t
      | otherwise -> TyScheme name' (recurse body) a
    TyArr arg ret a -> TyArr (recurse arg) (recurse ret) a
    TyTup tys a -> TyTup (recurse <$> tys) a
    TyCon name' _ -- TODO should this even be allowed?
        | DName name' == name -> value
        | otherwise -> t
    TyApp f x a -> TyApp (recurse f) (recurse x) a

-- | get the application spine of a type
spine :: Type a -> (Type a, [Type a])
spine (TyApp f x _) =
    let (x', xs') = spine x
    in (f, x':xs')
spine t = (t, [])

-- | Get the type arity of a kind
arityOfKind :: Kind a -> Int
arityOfKind KType{} = 0
arityOfKind (KArr _ ret _) = 1 + arityOfKind ret

-- | Construct a simple kind with the given type arity. Must be positive
kindWithArity :: Int -> Kind ()
kindWithArity n | n < 0 = error "cannot create kind with negative arity"
kindWithArity 0 = star
kindWithArity n = star *-> kindWithArity (n - 1)

-- combinators for constructing types


-- | construct a unit type
one :: Type ()
one = ttup []

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

-- | combinator for constructing user-defined types
tcon :: String -> Type ()
tcon name = TyCon name ()

-- | combinator for constructing type applications
tapp :: Type () -> Type () -> Type ()
tapp f x = TyApp f x ()

-- | alias for tapp
infixl 4 \\$
(\\$) :: Type () -> Type () -> Type ()
(\\$) = tapp

-- example: the type of the identity function
_ = "a" \/. uvar "a" \-> uvar "a"

-- kind combinators

-- | Type kind combinator
star :: Kind ()
star = KType ()

-- | Function kind combinator
infixr 3 *->
(*->) :: Kind () -> Kind () -> Kind ()
arg *-> ret = KArr arg ret ()
