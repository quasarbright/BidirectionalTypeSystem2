{-# LANGUAGE RankNTypes #-}

import Test.HUnit
import Common
import Exprs
import Types
import Environment
import Check
import Debug.Trace

teq :: (Eq a, Show a) => String -> a -> a -> Test
teq name a b = TestCase (assertEqual name a b)

tpass :: Test
tpass = TestCase $ assertEqual "pass" True True

tContextWF :: (Eq a, Show a) => String -> Context a -> Either (ContextWFError a) () -> Test
tContextWF name ctx expected = teq name expected (checkContextWellFormedness ctx)

tTypeWF :: (Eq a, Show a) => String -> Type a -> Context a -> Either (ContextWFError a) () -> Test
tTypeWF name t ctx expected = teq name expected (checkTypeWellFormedness ctx t)

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
        tContextWF "simple wf" simpleCtx (Right()),
        tTypeWF "one wf" one simpleCtx (Right()),
        tTypeWF "one->one wf" (one \-> one) simpleCtx (Right()),
        tTypeWF "a->one wf" (uvar "a" \-> one) simpleCtx (Right()),
        tTypeWF "b?->one wf" (evar "b" \-> one) simpleCtx (Right()),
        tTypeWF "forall d . d -> c wf" ("d" \/. uvar "d" \-> uvar "c") simpleCtx (Right()),
        tTypeWF "unbound uvar" (uvar "dd") simpleCtx (Left $ UnboundUVar "dd" ()),
        tTypeWF "unbound evar" (evar "dd") simpleCtx (Left $ UnboundEVar "dd" ()),
        tTypeWF "unbound evar in arg" (evar "dd" \-> one) simpleCtx (Left $ UnboundEVar "dd" ()),
        tTypeWF "unbound evar in ret" (one \-> evar "dd" \-> one) simpleCtx (Left $ UnboundEVar "dd" ()),
        tTypeWF "unbound evar in scheme" ("u" \/. one \-> evar "dd" \-> one) simpleCtx (Left $ UnboundEVar "dd" ()),
        tContextWF "simple+dup marker" (addEMarker "b" simpleCtx) (Left $ DupEMarker (EMarker "b")),
        tContextWF "simple+dup evar" (addEDecl "b" simpleCtx) (Left $ DupEVar (EDecl "b")),
        tContextWF "simple+badAnnot" (addVarAnnot "y" (one \-> uvar "sdf") simpleCtx) (Left $ UnboundUVar "sdf" ()),
        tContextWF "simple+dupAnnot" (addVarAnnot "absoluteUnit" (one \-> one) simpleCtx) (Left $ DupVar (VarAnnot "absoluteUnit" (one \-> one))),
        tContextWF "edecl then its marker" (simpleCtx |> addEDecl "d" |> addEMarker "d") (Left $ DupEVar (EMarker "d")),
        tContextWF "simple + bad esol" (recordESol "b" (uvar "r") simpleCtx) (Left $ UnboundUVar "r" ()),
        tContextWF "simple + good annot" (addVarAnnot "y" (one \-> uvar "a" \-> evar "b") simpleCtx) (Right ()),
        tContextWF "simple + good sol" (recordESol "b" (one \-> uvar "a") simpleCtx) (Right ()),
        tContextWF "dup uvar at beginning of env" (emptyContext |> addUDecl "a" |> addUDecl "a" |> addUDecl "b" |> addESol "c" one) (Left $ DupUVar (UDecl "a")),
        tpass
  ]

subtypeCtx =
  initialContext
  |> addUDecl "a"
  |> addEMarker "b"
  |> addEDecl "b"

tSubtypePass :: (Eq a, Show a) => Type a -> Type a -> Test
tSubtypePass a b = teq (show a++" <: "++show b) (Right ()) (runSubtype a b subtypeCtx)

tSubtypeError :: (Eq a, Show a) => Type a -> Type a -> TypeError a -> Test
tSubtypeError a b err = teq (show a++" <: "++show b) (Left err) (runSubtype a b subtypeCtx)

tSubtypeMismatch :: (Eq a, Show a) => Type a -> Type a -> Test
tSubtypeMismatch a b = tSubtypeError a b (Mismatch a b)

subtypeTests :: Test
subtypeTests = TestLabel "subtype tests" $ TestList
  [ tpass
  , tSubtypePass one one
  , tSubtypePass (uvar "a") (uvar "a")
  , tSubtypePass (evar "a") (evar "a")
  , tSubtypePass (evar "a" \-> one) (evar "a" \-> one)
  , tSubtypeMismatch one (uvar "a")
  , tSubtypeMismatch (uvar "a") one
  , tSubtypeMismatch (uvar "a") (uvar "b")
  , tSubtypeMismatch (uvar "a") (one \-> one)
  , tSubtypeMismatch (one \-> one) (uvar "a")
  , tSubtypeError (one \-> one) (uvar "a" \-> uvar "a") (Mismatch (uvar "a") one)
  , tSubtypeError (uvar "a" \-> uvar "a") (one \-> one) (Mismatch one (uvar "a"))
  , tSubtypeError (one \-> one) ("c" \/. uvar "c" \-> uvar "c") (Mismatch (uvar "c") one)
  , tSubtypeError (evar "c") (evar "c" \-> one) (OccursError (EName "c") (evar "c" \-> one))
  , tSubtypeError (evar "c" \-> one) (evar "c") (OccursError (EName "c") (evar "c" \-> one))
  ]

tests :: Test
tests = TestList
    [ ctxTests
    , subtypeTests
    ]

main :: IO Counts
main = runTestTT tests
