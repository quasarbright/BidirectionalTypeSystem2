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
  getFreeVars :: f a -> Set.Set String
  -- | for operator precedence
  getPrecedence :: f a -> Int
