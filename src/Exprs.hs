module Exprs where

import qualified Data.Set as Set
import Common
import Types

type VarName = String

data Expr a = Var VarName a
            | Unit a
            | Lambda VarName (Expr a) a
            | App (Expr a) (Expr a) a
            | Annot (Expr a) (Type a) a
            deriving(Eq, Ord)

instance Show (Expr a) where
  showsPrec p e =
    let p' = getPrecedence e in
    case e of
      Var name _ -> showString name
      Unit{} -> showString "()"
      Lambda x body _ -> showParen (p > p') $ showString "\\" . showString x . showString "." . showsPrec p' body
      App f x _ -> showParen (p > p') $ showsPrec p' f . showString " " . showsPrec (p'+1) x
      Annot e' t _ -> showParen (p > p') $ showsPrec p' e' . showString " :: " . showsPrec (p'+1) t

instance Functor Expr where
  fmap f (Var name a) = Var name (f a)
  fmap f (Unit a) = Unit (f a)
  fmap f (Lambda name e a) = Lambda name (fmap f e) (f a)
  fmap f (App g x a) = App (fmap f g) (fmap f x) (f a)
  fmap f (Annot e t a) = Annot (fmap f e) (fmap f t) (f a)

instance Tagged Expr where
  getTag (Unit a) = a
  getTag (Var _ a) = a
  getTag (Lambda _ _ a) = a
  getTag (App _ _ a) = a
  getTag (Annot _ _ a) = a

  setTag a (Unit _) = Unit a
  setTag a (Var name _) = Var name a
  setTag a (Lambda name body _) = Lambda name body a
  setTag a (App f x _) = App f x a
  setTag a (Annot e t _) = Annot e t a

instance ExprLike Expr where
  getFreeVars (Var name _) = Set.singleton name
  getFreeVars Unit{} = Set.empty
  getFreeVars (Lambda name body _) = Set.delete name (getFreeVars body)
  getFreeVars (App f x _) = Set.union (getFreeVars f) (getFreeVars x)
  getFreeVars (Annot e _ _) = getFreeVars e

  getPrecedence Var{} = 100
  getPrecedence Unit{} = 100
  getPrecedence Lambda{} = 3
  getPrecedence App{} = 4
  getPrecedence Annot{} = 1

-- combinators for easily building expressions

-- | make a variable value
var :: VarName -> Expr ()
var s = Var s ()

-- | make a unit value
unit :: Expr ()
unit = Unit ()

-- | lambda expression combinator
infixr 3 \.
(\.) :: VarName -> Expr () -> Expr ()
name \.  body = Lambda name body ()

-- | Function application combinator (high precedence)
infixl 4 \$
(\$) :: Expr () -> Expr () -> Expr ()
f \$ x = App f x ()

-- | annot value combinator
infixl 1 \::
(\::) :: Expr () -> Type () -> Expr ()
e \:: t = Annot e t ()

-- example: identity function
_ = "x" \. var "x" \:: "a" \/. tvar "a" \-> tvar "a"
