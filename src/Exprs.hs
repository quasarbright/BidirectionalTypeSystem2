module Exprs where

import qualified Data.Set as Set
import Common
import Types
import Data.List

data Expr a = Var String a
            -- ()
            | Unit a
            -- 12
            | EInt Int a
            -- \x.e
            | Lambda String (Expr a) a
            -- \x::A.e
            | LambdaAnnot String (Type a) (Expr a) a
            -- let x = e in e
            | Let String (Expr a) (Expr a) a
            -- let x::A = e in e
            | LetAnnot String (Type a) (Expr a) (Expr a) a
            -- e e
            | App (Expr a) (Expr a) a
            -- (e1, ..., en)
            | Tup [Expr a] a
            -- e::A
            | Annot (Expr a) (Type a) a

instance Show (Expr a) where
  showsPrec p e =
    let p' = getPrecedence e in
    case e of
      Var name _ -> shows (VName name)
      Unit{} -> showString "()"
      EInt n _ -> shows n
      Lambda x body _ -> showParen (p > p') $ showString "\\" . shows (VName x) . showString "." . showsPrec p' body
      LambdaAnnot x t body _ -> showParen (p > p') $ showString "\\(" . shows (VName x) . showString " :: " . shows t . showString ")." . showsPrec p' body
      Let x value body _ -> showString "let " . showString x . showString " = " . shows value . showString " in " . shows body
      LetAnnot x t value body _ -> showString "let (" . showString x . showString " :: " . shows t . showString ") = " . shows value . showString " in " . shows body
      App f x _ -> showParen (p > p') $ showsPrec p' f . showString " " . showsPrec (p'+1) x
      Tup es _ -> showParen True $ showString . intercalate ", " $ show <$> es
      Annot e' t _ -> showParen (p > p') $ showsPrec p' e' . showString " :: " . showsPrec (p'+1) t

instance Eq (Expr a) where
  Var name _ == Var name' _ = name == name'
  Var{} == _ = False
  Unit{} == Unit{} = True
  Unit{} == _ = False
  EInt n _ == EInt n' _ = n == n'
  EInt{} == _ = False
  Lambda name body _ == Lambda name' body' _ = name == name' && body == body'
  Lambda{} == _ = False
  LambdaAnnot x t body _ == LambdaAnnot x' t' body' _ = (x, t, body) == (x', t', body')
  LambdaAnnot{} == _ = False
  Let x value body _ == Let x' value' body' _ = (x, value, body) == (x', value', body')
  Let{} == _ = False
  LetAnnot x t value body _ == LetAnnot x' t' value' body' _ = (x, t, value, body) == (x', t', value', body')
  LetAnnot{} == _ = False
  App f x _ == App f' x' _ = f == f' && x == x'
  App{} == _ = False
  Tup es _ == Tup es' _ = es == es'
  Tup{} == _ = False
  Annot e t _ == Annot e' t' _ = e == e' && t == t'
  Annot{} == _ = False

instance Functor Expr where
  fmap f (Var name a) = Var name (f a)
  fmap f (Unit a) = Unit (f a)
  fmap f (EInt n a) = EInt n (f a)
  fmap f (Lambda name e a) = Lambda name (fmap f e) (f a)
  fmap f (LambdaAnnot name t e a) = LambdaAnnot name (fmap f t) (fmap f e) (f a)
  fmap f (Let x e body a) = Let x (fmap f e) (fmap f body) (f a)
  fmap f (LetAnnot x t e body a) = LetAnnot x (fmap f t) (fmap f e) (fmap f body) (f a)
  fmap f (App g x a) = App (fmap f g) (fmap f x) (f a)
  fmap f (Tup es a) = Tup (fmap f <$> es) (f a)
  fmap f (Annot e t a) = Annot (fmap f e) (fmap f t) (f a)

instance Tagged Expr where
  getTag (Unit a) = a
  getTag (EInt _ a) = a
  getTag (Var _ a) = a
  getTag (Lambda _ _ a) = a
  getTag (LambdaAnnot _ _ _ a) = a
  getTag (Let _ _ _ a) = a
  getTag (LetAnnot _ _ _ _ a) = a
  getTag (App _ _ a) = a
  getTag (Tup _ a) = a
  getTag (Annot _ _ a) = a

  setTag a (Unit _) = Unit a
  setTag a (EInt n _) = EInt n a
  setTag a (Var name _) = Var name a
  setTag a (Lambda name body _) = Lambda name body a
  setTag a (LambdaAnnot name t body _) = LambdaAnnot name t body a
  setTag a (Let x e body _) = Let x e body a
  setTag a (LetAnnot x t e body _) = LetAnnot x t e body a
  setTag a (App f x _) = App f x a
  setTag a (Tup es _) = Tup es a
  setTag a (Annot e t _) = Annot e t a

instance ExprLike Expr where
  getFreeVars (Var name _) = Set.singleton (VName name)
  getFreeVars Unit{} = Set.empty
  getFreeVars EInt{} = Set.empty
  getFreeVars (Lambda name body _) = Set.delete (VName name) (getFreeVars body)
  getFreeVars (LambdaAnnot name _ body _) = Set.delete (VName name) (getFreeVars body)
  getFreeVars (Let x e body _) = Set.union (getFreeVars e) (Set.delete (VName x) $ getFreeVars body)
  getFreeVars (LetAnnot x _ e body _) = Set.union (getFreeVars e) (Set.delete (VName x) $ getFreeVars body)
  getFreeVars (App f x _) = Set.union (getFreeVars f) (getFreeVars x)
  getFreeVars (Tup es _) = Set.unions (getFreeVars <$> es)
  getFreeVars (Annot e _ _) = getFreeVars e

  getPrecedence Var{} = 100
  getPrecedence Unit{} = 100
  getPrecedence EInt{} = 100
  getPrecedence Lambda{} = 3
  getPrecedence LambdaAnnot{} = 3
  getPrecedence Let{} = 3
  getPrecedence LetAnnot{} = 3
  getPrecedence App{} = 4
  getPrecedence Tup{} = 100
  getPrecedence Annot{} = 1

-- combinators for easily building expressions

-- | make a variable value
var :: String -> Expr ()
var s = Var s ()

-- | make a unit value
unit :: Expr ()
unit = Unit ()

-- | make an integer value
int :: Int -> Expr ()
int n = EInt n ()

-- | lambda expression combinator
infixr 3 \.
(\.) :: String -> Expr () -> Expr ()
name \.  body = Lambda name body ()

-- | annotated lambda expression combinator
lamAnnot :: String -> Type () -> Expr () -> Expr ()
lamAnnot x t body = LambdaAnnot x t body ()

-- | let expression combinator
elet :: String -> Expr () -> Expr () -> Expr ()
elet x e body = Let x e body ()

-- | annotated let expression combinator
letAnnot :: String -> Type () -> Expr () -> Expr () -> Expr ()
letAnnot x t e body = LetAnnot x t e body ()

-- | Function application combinator (high precedence)
infixl 4 \$
(\$) :: Expr () -> Expr () -> Expr ()
f \$ x = App f x ()

-- | Tuple expression combinator
tup :: [Expr ()] -> Expr ()
tup es = Tup es ()

-- | annot value combinator
infixl 1 \::
(\::) :: Expr () -> Type () -> Expr ()
e \:: t = Annot e t ()

-- example: identity function
_ = "x" \. var "x" \:: "a" \/. uvar "a" \-> uvar "a"
