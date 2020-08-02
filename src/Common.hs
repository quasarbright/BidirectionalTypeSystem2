module Common where

import qualified Data.Set as Set

infixl 1 |>
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- | A tagged value. Useful for tagged expressions, types, etc.
class Functor f => Tagged f where
  -- | get the tag of this Tagged value
  getTag :: f a -> a
  -- | Set the tag of this tagged value, not affecting children
  setTag :: a -> f a -> f a

-- | exprs and types
class Tagged f => ExprLike f where
  -- | get the set of variable names occurring free in the expression
  getFreeVars :: f a -> Set.Set Name
  -- | for operator precedence
  getPrecedence :: f a -> Int

-- | union type for names
-- Usually, strings will be passed around. Names are just for when you need to tag a string with its name type
-- or display a string as a particular name
data Name = VName String -- expr var name
          | UName String -- type universal name
          | EName String -- type existential name
          | DName String -- type Constructor name
          | CName String -- Value Constructor name

          deriving(Eq, Ord)

instance Show Name where
  show n = case n of
    VName name -> name
    UName name -> name
    EName name -> name ++ "?"
    DName name -> name
    CName name -> name
