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
          expectedCtx =
            emptyContext
            |> addVarAnnot "absoluteUnit" one
            |> addUDecl "a"
            |> addEMarker "b"
            |> addEDecl "b$5" -- ret
            |> addEDecl "b$6" -- arg
            |> addESol "b" (evar "b$6" \-> evar "b$5")
            |> addUDecl "c"
          expected = ("b$6", "b$5", expectedCtx)
        in teq "replace one with many" expected (instArrReplacement "b" () ctx)
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

instSubtypeCtx =
  emptyContext
  |> addVarAnnot "x" one
  |> addUDecl "z"
  |> addEMarker "y"
  |> addEDecl "y"
  |> addEDecl "g"

-- | for simple subtype tests that don't affect the context and use subtypeCtx
tSubtypePass :: (Eq a, Show a) => Type a -> Type a -> Test
tSubtypePass a b = tSubtypePassInst subtypeCtx a b subtypeCtx

-- | same as other version, but take in an input context and care about the output context
tSubtypePassInst :: (Eq a, Show a) => Context a -> Type a -> Type a -> Context a -> Test
tSubtypePassInst ctx a b ctx' = teq (show a++" <: "++show b) (Right ctx') (runSubtype a b ctx)

tSubtypeError :: (Eq a, Show a) => Type a -> Type a -> TypeError a -> Test
tSubtypeError = tSubtypeErrorInst subtypeCtx

-- | same as other version, but take in an input context
tSubtypeErrorInst :: (Eq a, Show a) => Context a -> Type a -> Type a -> TypeError a -> Test
tSubtypeErrorInst ctx a b err = teq (show a++" <: "++show b) (Left err) (runSubtype a b ctx)

tSubtypeMismatch :: (Eq a, Show a) => Type a -> Type a -> Test
tSubtypeMismatch a b = tSubtypeError a b (Mismatch a b)

subtypeTests :: Test
subtypeTests = TestLabel "subtype tests" $ TestList
  [ tpass
  -- no instantiation
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
  -- instantiation
  , tSubtypePassInst emptyContext ("a" \/. uvar "a" \-> uvar "a") (one \-> one) emptyContext
  , tSubtypePassInst instSubtypeCtx ("a" \/. uvar "a" \-> uvar "a") (one \-> one) instSubtypeCtx
  -- shape -> hexagon <: hexagon -> shape
  , tSubtypePassInst instSubtypeCtx ((one \-> one) \-> ("a" \/. uvar "a" \-> uvar "a")) (("a" \/. uvar "a" \-> uvar "a") \-> (one \-> one)) instSubtypeCtx
  , tSubtypePassInst instSubtypeCtx ("a" \/. uvar "a" \-> uvar "a") ("b" \/. uvar "b" \-> uvar "b") instSubtypeCtx
  , tSubtypePassInst instSubtypeCtx ("a" \/. uvar "a" \-> uvar "a") ("a" \/. uvar "a" \-> uvar "a") instSubtypeCtx
  , tSubtypePassInst instSubtypeCtx (evar "y") one (recordESol "y" one instSubtypeCtx)
  , tSubtypePassInst instSubtypeCtx one (evar "y") (recordESol "y" one instSubtypeCtx)
  , let
      expectedCtx =
        emptyContext
        |> addVarAnnot "x" one
        |> addUDecl "z"
        |> addEMarker "y"
        |> addESol "y$5" one
        |> addESol "y$6" one
        |> addESol "y" (evar "y$6" \-> evar "y$5")
        |> addEDecl "g"
    in
    tSubtypePassInst instSubtypeCtx (evar "y") (one \-> one) (recordESol "y" (one \-> one) expectedCtx)
  , let
    expectedCtx =
      emptyContext
      |> addVarAnnot "x" one
      |> addUDecl "z"
      |> addEMarker "y"
      |> addESol "y$5" one
      |> addESol "y$6" one
      |> addESol "y" (evar "y$6" \-> evar "y$5")
      |> addEDecl "g"
    in
    tSubtypePassInst instSubtypeCtx (one \-> one) (evar "y") (recordESol "y" (one \-> one) expectedCtx)
  , tSubtypePassInst instSubtypeCtx (evar "y") (evar "g") (recordESol "g" (evar "y") instSubtypeCtx)
  , tSubtypePassInst instSubtypeCtx (evar "g") (evar "y") (recordESol "g" (evar "y") instSubtypeCtx)
  , tSubtypePassInst instSubtypeCtx (evar "g") (evar "y") (recordESol "g" (evar "y") instSubtypeCtx)
  , tSubtypePassInst instSubtypeCtx (evar "y") (uvar "z") (recordESol "y" (uvar "z") instSubtypeCtx)
  , tSubtypePassInst instSubtypeCtx (uvar "z") (evar "y") (recordESol "y" (uvar "z") instSubtypeCtx)
  , let
     expectedCtx =
       emptyContext
       |> addVarAnnot "x" one
       |> addUDecl "z"
       |> addEMarker "y"
       |> addESol "y$6" (uvar "a")
       |> addESol "y$7" (uvar "a")
       |> addESol "y" (evar "y$7" \-> evar "y$6")
       |> addEDecl "g"
    in
    tSubtypePassInst instSubtypeCtx (evar "y") ("a" \/. uvar "a" \-> uvar "a") expectedCtx
  , let
     expectedCtx =
       emptyContext
       |> addVarAnnot "x" one
       |> addUDecl "z"
       |> addEMarker "y"
       -- this makes sense bc y? has to be less polymorphic then the id function.
       -- when this type is "collapsed", it'll be collapsed to a particular, monomorphic identity function,
       -- possibly on the right-hand-side of a universal quantifier. The collapse will just solve y$8. Cool!
       |> addEDecl "y$8"
       |> addESol "y$9" (evar "y$8")
       |> addESol "y" (evar "y$9" \-> evar "y$8")
       |> addEDecl "g"
    in
    tSubtypePassInst instSubtypeCtx ("a" \/. uvar "a" \-> uvar "a") (evar "y") expectedCtx

  , tSubtypeErrorInst instSubtypeCtx (one \-> one) ("a" \/. uvar "a" \-> uvar "a") (Mismatch (uvar "a") one)
  , tSubtypeErrorInst instSubtypeCtx (("a" \/. uvar "a" \-> uvar "a") \-> (one \-> one)) ((one \-> one) \-> ("a" \/. uvar "a" \-> uvar "a")) (Mismatch (uvar "a") one)
  , tpass
  ]

{-

check if the identity function is a subtype of the unit-only identity function

                                             [] |- \/a.a -> a  <:  1 -> 1 -| []
                                  ------------------------------------------------------- <: forall L
                                  [MARK a?, a?] |- a? -> a?  <: 1 -> 1 -| [MARK a?, a?=1]
---------------------------------------------------------------------------------------------------------------------------------------------- <: ->
                                                               [MARK a?, a?=1] |- [MARK a?, a?=1][a?] <: [MARK a?, a?=1][1] |- [MARK a?, a?=1]
[MARK a?, a?] |- 1 <: a? -| [MARK a?, a?=1]                                      [MARK a?, a?=1] |- 1 <: 1 |- [MARK a?, a?=1]
-------------------------------------------- <: InstantiateR   ------------------------------------------------------------------------------- <: Unit
[MARK a?, a?] |- 1 <=: a? -| [MARK a?, a?=1]
-------------------------------------------- InstRSolve

-}

tSynth :: (Eq a, Show a) => Context a -> Expr a -> Type a -> Context a -> Test
tSynth ctx e t ctx' = teq (show e++" => "++show t) (Right (t, ctx')) (runTypeSynth e ctx)

tSynthErr :: (Eq a, Show a) => Context a -> Expr a -> TypeError a -> Test
tSynthErr ctx e err = teq (show e++" =/> ERROR: "++show err) (Left err) (runTypeSynth e ctx)

--tSynthSimplify :: (Eq a, Show a) => Context a -> Expr a -> Type a -> Context a -> Test
--tSynthSimplify ctx e t ctx' = teq (show e++" => "++show t) (Right (t, ctx')) (simplify <$> runTypeSynth e ctx)
--  where
--    simplify (typ, finalCtx) = (contextAsSubstitution finalCtx typ, finalCtx)

synthCheckTests = TestLabel "type synthesis and checking" $ TestList
  [ tpass
  , tSynth emptyContext unit one emptyContext
  , tSynth emptyContext (int 1) tint emptyContext
  , let ctx = emptyContext |> addVarAnnot "x" one
    in tSynth ctx (var "x") one ctx
  -- thought this was weird at first and it should just synthesize (). But I tried to cause a mismatch with this behavior
  -- and everything just worked, so I guess it's ok. That a$0? is equal to 1, but it just didn't get substituted
  , tSynth emptyContext (("x" \. var "x") \$ unit) (evar "a$0") (emptyContext |> addESol "a$0" one |> addESol "b$1" (evar "a$0"))
  , tSynth emptyContext ("u" \. var "u" \:: one \-> one) (one \-> one) emptyContext
  -- try to cause a mismatch with the weird unsubstituted existential mentioned earlier, but it worked fine
  , tSynth emptyContext (("u" \. var "u" \:: one \-> one) \$ (("x" \. var "x") \$ unit)) one (emptyContext |> addESol "a$2" one |> addESol "b$3" (evar "a$2"))
  , tSynth emptyContext (("u" \. var "u" \:: tint \-> tint) \$ (("x" \. var "x") \$ int 1)) tint (emptyContext |> addESol "a$2" tint |> addESol "b$3" (evar "a$2"))
  -- polymorphic identity function
  , tSynth emptyContext id_ ("a" \/. uvar "a" \-> uvar "a") emptyContext
  -- using polymorphic identity function simply. get unsubstituted existential again
  , tSynth emptyContext (id_ \$ unit) (evar "a$4") (emptyContext |> addESol "a$4" one)
  -- try to cause mismatch with unsubstituted existential, but it works fine
  , tSynth emptyContext (("u" \. var "u" \:: one \-> one) \$ (id_ \$ unit)) one (emptyContext |> addESol "a$6" one)
  , let
      ctx' =
        emptyContext
        |> addESol "a$4$8" one
        |> addESol "a$4$9" one
        |> addESol "a$4" (evar "a$4$9" \-> evar "a$4$8")
        |> addESol "a$17" one
    in tSynth emptyContext (id_ \$ ("u" \. var "u" \:: one \-> one) \$ (id_ \$ unit)) one ctx'
  , let t = ("a" \/. "b" \/.
                      ("c" \/. uvar "c" \-> uvar "c") -- id function. note inner forall
                      \-> (uvar "a" \-> uvar "b") -- f
                      \-> uvar "a" -- x
                      \-> uvar "b") -- f x
    in tSynth emptyContext idApp t emptyContext
  -- use polymorphic identity function
  , tSynth emptyContext (idApp \$ id_ \$ id_ \$ unit) (evar "a$20") (emptyContext |> addESol "a$20" one |> addESol "b$22" (evar "a$20"))
  , tSynthErr emptyContext (idApp \$ id_ \$ unit) (Mismatch one (evar "a$20" \-> evar "b$22"))
  -- different types for branches of if
  , tSynthErr emptyContext (if_ \$ true \$ unit \$ ("x" \. unit \:: "a" \/. uvar "a" \-> one )) (Mismatch (evar "a$33" \-> one) one)
  -- successful if
  , tSynth emptyContext (if_ \$ true \$ unit \$ unit) one (emptyContext |> addESol "a$8" one)
  -- \x.x x infinite type
  , tSynthErr emptyContext ("x" \. var "x" \$ var "x") (OccursError (EName "a$0$6") (evar "a$0$6" \-> evar "a$0$5"))
  -- y combinator can't type check :(
  , tSynthErr emptyContext ("f" \. ("x" \. var "f" \$ (var "x" \$ var "x")) \$ ("x" \. var "f" \$ (var "x" \$ var "x"))) (OccursError (EName "a$5$14") (evar "a$5$14" \-> evar "a$5$13"))
  -- apply non-function
  , tSynthErr emptyContext (unit \$ unit) (Mismatch (evar "a" \-> evar "b") one)
  ]

tests :: Test
tests = TestList
    [ ctxTests
    , subtypeTests
    , synthCheckTests
    ]

main :: IO Counts
main = runTestTT tests
