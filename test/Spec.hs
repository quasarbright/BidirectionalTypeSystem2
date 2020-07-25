{-# LANGUAGE RankNTypes #-}

import Exprs
import Types
import Common

id_ :: Expr ()
id_ = "x" \. var "x" \:: "a" \/. tvar "a" \-> tvar "a"

true :: Expr ()
true = ("x" \. "y" \. var "x") \:: ("a" \/. "b" \/. tvar "a" \-> tvar "b" \-> tvar "a")

false :: Expr ()
false = ("x" \. "y" \. var "y") \:: ("a" \/. "b" \/. tvar "a" \-> tvar "b" \-> tvar "b")

if_ :: Expr ()
if_ = ("cond" \. "thn" \. "els" \. var "cond" \$ var "thn" \$ var "els")
      \:: ("a" \/. (tvar "a" \-> tvar "a" \-> tvar "a") \-> tvar "a" \-> tvar "a" \-> tvar "a")


-- | an example of higher rank polymorphism. see @idAppHask@ for the Haskell equivalent
idApp :: Expr ()
idApp = ("id" \. "f" \. "x" \. (var "id" \$ var "f") \$ (var "id" \$ var "x"))
        \:: ("a" \/. "b" \/.
          ("c" \/. tvar "c" \-> tvar "c") -- id function. note inner forall
          \-> (tvar "a" \-> tvar "b") -- f
          \-> tvar "a" -- x
          \-> tvar "b") -- f x

-- | higher rank polymorphism in haskell. Note the inner forall
idAppHask :: forall a b . (forall c . c -> c) -> (a -> b) -> a -> b
idAppHask idFun f x = idFun f (idFun x)

main :: IO ()
main = putStrLn "Test suite not yet implemented"
