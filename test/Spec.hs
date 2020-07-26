{-# LANGUAGE RankNTypes #-}

import Test.HUnit
import Common
import Exprs
import Types
import Environment

teq :: (Eq a, Show a) => String -> a -> a -> Test
teq name a b = TestCase (assertEqual name a b)

tpass :: Test
tpass = TestCase $ assertEqual "pass" True True


id_ :: Expr ()
id_ = "x" \. var "x" \:: "a" \/. uvar "a" \-> uvar "a"

true :: Expr ()
true = ("x" \. "y" \. var "x") \:: ("a" \/. "b" \/. uvar "a" \-> uvar "b" \-> uvar "a")

false :: Expr ()
false = ("x" \. "y" \. var "y") \:: ("a" \/. "b" \/. uvar "a" \-> uvar "b" \-> uvar "b")

if_ :: Expr ()
if_ = ("cond" \. "thn" \. "els" \. var "cond" \$ var "thn" \$ var "els")
      \:: ("a" \/. (uvar "a" \-> uvar "a" \-> uvar "a") \-> uvar "a" \-> uvar "a" \-> uvar "a")

-- | an example of higher rank polymorphism. see @idAppHask@ for the Haskell equivalent
idApp :: Expr ()
idApp = ("id" \. "f" \. "x" \. (var "id" \$ var "f") \$ (var "id" \$ var "x"))
        \:: ("a" \/. "b" \/.
          ("c" \/. uvar "c" \-> uvar "c") -- id function. note inner forall
          \-> (uvar "a" \-> uvar "b") -- f
          \-> uvar "a" -- x
          \-> uvar "b") -- f x

-- | higher rank polymorphism in haskell. Note the inner forall
idAppHask :: forall a b . (forall c . c -> c) -> (a -> b) -> a -> b
idAppHask idFun f x = idFun f (idFun x)

simpleCtx :: Context ()
simpleCtx =
  emptyContext
  |> addVarAnnot "absoluteUnit" one
  |> addUDecl "a"
  |> addEMarker "b"
  |> addEDecl "b"
  |> addUDecl "c"

substitutionCtx :: Context ()
substitutionCtx =
  emptyContext
  |> addEMarker "a"
  |> addESol "a" (one \-> one)
  |> addEMarker "b"
  |> addEDecl "b"
  |> addUDecl "c"
  |> addVarAnnot "id" ("a" \/. uvar "a" \-> uvar "a")

ctxTests = TestLabel "context tests" $ TestList [
        let
          ctx =
            emptyContext
            |> addVarAnnot "absoluteUnit" one
            |> addUDecl "b"
            |> addEMarker "a"
            |> addEDecl "a"
            |> addUDecl "d"
          expected =
            emptyContext
            |> addVarAnnot "absoluteUnit" one
            |> addUDecl "b"
        in  teq "after marker" expected (removeItemsAfterEMarker "a" ctx)
        ,
        let
          ctx = simpleCtx
          expected =
            emptyContext
            |> addVarAnnot "absoluteUnit" one
            |> addUDecl "a"
            |> addEMarker "b"
            |> addESol "b" (one \-> one)
            |> addUDecl "c"
        in teq "record e sol" expected (recordESol "b" (one \-> one) ctx)
        ,
        let
          ctx = simpleCtx
          expected =
            emptyContext
            |> addVarAnnot "absoluteUnit" one
            |> addUDecl "a"
            |> addEMarker "b"
            |> addEDecl "b$5" -- ret
            |> addEDecl "b$6" -- arg
            |> addESol "b" (evar "b$6" \-> evar "b$5")
            |> addUDecl "c"
        in teq "replace one with many" expected (instLArrReplacement "b" () ctx)
        ,
        let
          ctx = substitutionCtx
          expected = one \-> one
        in teq "substitution1" expected (contextAsSubstitution ctx (evar "a"))
        ,
        let
          ctx = substitutionCtx
          expected = (one \-> one) \-> (one \-> one)
        in teq "substitution2" expected (contextAsSubstitution ctx (evar "a" \-> evar "a"))
        ,
        let
          ctx = substitutionCtx
          expected = (one \-> one) \-> evar "b"
        in teq "substitution3" expected (contextAsSubstitution ctx (evar "a" \-> evar "b"))
        ,
        let
          ctx = substitutionCtx
          expected = "d" \/. (uvar "c" \-> uvar "d" \-> one \-> one)
        in teq "substitution4" expected (contextAsSubstitution ctx ("d" \/. (uvar "c" \-> uvar "d" \-> evar "a")))
        ,
        tpass
  ]

tests :: Test
tests = TestList
    [ ctxTests
    , tpass
    ]

main :: IO Counts
main = runTestTT tests
