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

-- | a less polymorphic example of higher rank polymorphism using annotated lambdas.
-- the limitation with annotated lambdas is that you can't mention the same universal in different arguments' annotations
idAppAnnot :: Expr ()
idAppAnnot = lamAnnot "id" ("a" \/. uvar "a" \-> uvar "a") $
             lamAnnot "f" (one \-> one) $
             lamAnnot "x" one $
             var "id" \$ var "f" \$ (var "id" \$ var "x")

-- | higher rank polymorphism let binding followed by its usage
idAppLetWithUse :: Expr ()
idAppLetWithUse = letAnnot "idApp" ("a" \/. "b" \/. ("c" \/. uvar "c" \-> uvar "c") \-> (uvar "a" \-> uvar "b") \-> uvar "a" \-> uvar "b")
           ("id"\."f"\."x"\.  var "id" \$ var "f" \$ (var "id" \$ var "x"))
           (var "idApp" \$ id_ \$ id_ \$ unit)

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
          ctx = emptyContext |> addUDecl "b" |> addUDecl "a" |> addUDecl "a" |> addUDecl "c"
          expected = emptyContext |> addUDecl "b" |> addUDecl "a"
        in teq "dup uvar removal" expected (removeItemsAfterUDecl "a" ctx)
        ,
        let
          ctx = emptyContext |> addUDecl "b" |> addUDecl "a" |> addUDecl "d" |> addUDecl "a" |> addUDecl "c"
          expected = emptyContext |> addUDecl "b" |> addUDecl "a" |> addUDecl "d"
        in teq "dup uvar removal" expected (removeItemsAfterUDecl "a" ctx)
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
        , teq "substitutionTup" (ttup [one \-> one, one, evar "b"]) (contextAsSubstitution substitutionCtx $ ttup [evar "a", one, evar "b"])
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
  emptyContext
  |> addUDecl "a"
  |> addEMarker "b"
  |> addEDecl "b"
  |> addUDecl "q"

instSubtypeCtx =
  emptyContext
  |> addVarAnnot "x" one
  |> addUDecl "z"
  |> addEMarker "y"
  |> addEDecl "y"
  |> addEDecl "g"

dataCtx =
    initialContext
    |> addUDecl "a"
    |> addEMarker "b"
    |> addEDecl "b"
    |> addUDecl "q"

-- | for simple subtype tests that don't affect the context and use subtypeCtx
tSubtypePass :: (Eq a, Show a) => Type a -> Type a -> Test
tSubtypePass a b = tSubtypePassInst subtypeCtx a b subtypeCtx

-- | same as other version, but take in an input context and care about the output context
tSubtypePassInst :: (Eq a, Show a) => Context a -> Type a -> Type a -> Context a -> Test
tSubtypePassInst ctx a b ctx' = teq (show a++" <: "++show b) (Right ctx') actual
  where
    actual = case runSubtype a b ctx of
      Left err -> Left err
      Right s -> Right (stateContext s)

tSubtypeError :: (Eq a, Show a) => Type a -> Type a -> TypeError a -> Test
tSubtypeError = tSubtypeErrorInst subtypeCtx

-- | same as other version, but take in an input context
tSubtypeErrorInst :: (Eq a, Show a) => Context a -> Type a -> Type a -> TypeError a -> Test
tSubtypeErrorInst ctx a b err = teq (show a++" <: "++show b) (Left err) actual
  where
    actual = case runSubtype a b ctx of
      Left (err, _) -> Left err
      Right r -> Right r

tSubtypeMismatch :: (Eq a, Show a) => Type a -> Type a -> Test
tSubtypeMismatch a b = tSubtypeError a b (Mismatch b a)

subtypeTests :: Test
subtypeTests = TestLabel "subtype tests" $ TestList
  [ tpass
  -- no instantiation
  , tSubtypePass tint tint
  , tSubtypePass one one
  , tSubtypePass (uvar "a") (uvar "a")
  , tSubtypeError (uvar "z") (uvar "z") (TypeWFError $ UnboundUVar "z" ())
  , tSubtypePass (evar "b") (evar "b")
  , tSubtypePass (evar "b" \-> one) (evar "b" \-> one)
  , tSubtypePass (ttup [tint, tint, tint]) (ttup [tint, tint, tint])
  , tSubtypePass (ttup [tint, tint, tint \-> tint]) (ttup [tint, tint, tint \-> tint])
  , tSubtypeMismatch (ttup [tint, tint]) (ttup [tint, tint, tint])
  , tSubtypeError (ttup [tint, tint]) (ttup [tint, tint \-> tint]) (Mismatch (tint \-> tint) tint)
  , tSubtypePassInst dataCtx (tcon "Bool") (tcon "Bool") dataCtx
  , tSubtypePassInst dataCtx (tcon "List" \\$ tint) (tcon "List" \\$ tint) dataCtx
  , tSubtypeErrorInst dataCtx (tcon "List" \\$ tint) (tcon "List" \\$ one) (Mismatch one tint)
  , tSubtypeError (evar "z") one (ContextItemNotFound (EDecl "z"))
  , tSubtypeMismatch one tint
  , tSubtypeMismatch tint one
  , tSubtypeMismatch one (uvar "a")
  , tSubtypeMismatch (uvar "a") one
  , tSubtypeMismatch (uvar "a") (uvar "q")
  , tSubtypeMismatch (uvar "a") (one \-> one)
  , tSubtypeMismatch (one \-> one) (uvar "a")
  , tSubtypeError (tint \-> tint) (one \-> one) (Mismatch tint one)
  , tSubtypeError (one \-> one) (tint \-> tint) (Mismatch one tint)
  , tSubtypeError (one \-> one) (uvar "a" \-> uvar "a") (Mismatch one (uvar "a"))
  , tSubtypeError (uvar "a" \-> uvar "a") (one \-> one) (Mismatch (uvar "a") one)
  , tSubtypeError (one \-> one) ("c" \/. uvar "c" \-> uvar "c") (Mismatch one (uvar "c"))
  , tSubtypeError (evar "b") (evar "b" \-> one) (OccursError (EName "b") (evar "b" \-> one))
  , tSubtypeError (evar "b" \-> one) (evar "b") (OccursError (EName "b") (evar "b" \-> one))
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

  , tSubtypeErrorInst instSubtypeCtx (one \-> one) ("a" \/. uvar "a" \-> uvar "a") (Mismatch one (uvar "a"))
  , tSubtypeErrorInst instSubtypeCtx (("a" \/. uvar "a" \-> uvar "a") \-> (one \-> one)) ((one \-> one) \-> ("a" \/. uvar "a" \-> uvar "a")) (Mismatch one (uvar "a"))
  , tSubtypeError (evar "b" \-> evar "b") (tint \-> (tint \-> tint)) (Mismatch (tint \-> tint) tint)
  , tSubtypePassInst dataCtx ("a" \/. uvar "a") (ttup [tint, ttup [tint, one]]) dataCtx
  , tSubtypeError (ttup [evar "b", evar "b"]) (ttup [tint, tint \-> tint]) (Mismatch (tint \-> tint) tint)
  , tSubtypePassInst subtypeCtx (ttup [evar "b", evar "b"]) (ttup [tint, tint]) (subtypeCtx |> recordESol "b" tint)
  , tSubtypePassInst subtypeCtx ("g" \/. ttup [uvar "g", uvar "g"]) (ttup [tint, tint]) subtypeCtx
  , tSubtypePassInst dataCtx ("a" \/. uvar "a") (tcon "List" \\$ tint) dataCtx
  , tSubtypePassInst dataCtx ("a" \/. tcon "List" \\$ uvar "a") (tcon "List" \\$ tint) dataCtx
  , tSubtypePassInst dataCtx (tcon "List" \\$ ("a" \/. uvar "a" \-> uvar "a")) (tcon "List" \\$ (tint \-> tint)) dataCtx
  , tSubtypePassInst dataCtx (tcon "List" \\$ ("a" \/. uvar "a" \-> uvar "a")) (tcon "List" \\$ (tcon "Bool" \-> tcon "Bool")) dataCtx
  , tSubtypeErrorInst dataCtx (tcon "Bool") (tcon "List" \\$ tint) (Mismatch (tcon "List" \\$ tint) (tcon "Bool"))
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
tSynth ctx e t ctx' = teq (show e++" => "++show t) (Right (t, ctx')) actual
  where
    actual = case runTypeSynth e ctx of
      Left err -> Left err
      Right (t', s) -> Right (t',stateContext s)

-- | like tSynth, except it simplifies the actual type and ignores the output context
tSynthSimple :: (Eq a, Show a) => Context a -> Expr a -> Type a -> Test
tSynthSimple ctx e t = teq (show e++" => "++show t) (Right t) (fst <$> runTypeSynthSimplify e ctx)

tSynthErr :: (Eq a, Show a) => Context a -> Expr a -> TypeError a -> Test
tSynthErr ctx e err = teq (show e++" =/> ERROR: "++show err) (Left err) actual
  where
    actual = case runTypeSynth e ctx of
      Left (err,_) -> Left err
      Right r -> Right r

tCheck :: (Eq a, Show a) => Context a -> Expr a -> Type a -> Context a -> Test
tCheck ctx e t ctx' = teq (show e++" <= "++show t) (Right ctx') actual
  where
    actual = case runTypeCheck e t ctx of
      Left err -> Left err
      Right s -> Right (stateContext s)

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
  -- simple annotated lambda
  , tSynth emptyContext (lamAnnot "x" one (var "x")) (one \-> evar "b$0") (emptyContext |> addESol "b$0" one)
  -- simple let statement
  , tSynthSimple emptyContext (elet "x" unit (var "x")) one
  -- simple annotated let statement
  , tSynthSimple emptyContext (letAnnot "x" one unit (var "x")) one
  , tSynthSimple emptyContext (letAnnot "id" (one \-> one) ("x" \. var "x") (var "id" \$ unit)) one
  , tSynthSimple emptyContext (elet "id" ("x" \. var "x") (var "id" \$ unit)) one
  , tSynth emptyContext (letAnnot "id" ("a" \/. uvar "a" \-> uvar "a") ("x" \. var "x") (var "id" \$ unit)) (evar "b$4") (emptyContext |> addESol "b$4" one)
  , tSynth emptyContext (letAnnot "id" ("a" \/. uvar "a" \-> uvar "a") ("x" \. var "x") (var "id" \$ var "id" \$ (var "id" \$ unit))) (evar "b$4") (emptyContext |> addESol "b$4" one)
  -- use polymorphic identity function
  , tSynth emptyContext (idApp \$ id_ \$ id_ \$ unit) (evar "a$20") (emptyContext |> addESol "a$20" one |> addESol "b$22" (evar "a$20"))
  -- use annotated polymorphic identity function
  , tSynthSimple emptyContext (idAppAnnot \$ id_ \$ id_ \$ unit) one
  -- use let-annotated polymorphic identity function
  , tSynthSimple emptyContext idAppLetWithUse one
  , tSynthErr emptyContext (idApp \$ id_ \$ unit) (Mismatch (evar "a$20" \-> evar "b$22") one)
  -- different types for branches of if
  -- TODO make it so it mismatches with the universal type. When you instantiate a scheme, catch a left if that's possible
  , tSynthErr emptyContext (if_ \$ true \$ unit \$ ("x" \. unit \:: "a" \/. uvar "a" \-> one )) (Mismatch one (evar "a$33" \-> one))
  -- successful if
  , tSynth emptyContext (if_ \$ true \$ unit \$ unit) one (emptyContext |> addESol "a$8" one)
  -- \x.x x infinite type
  , tSynthErr emptyContext ("x" \. var "x" \$ var "x") (OccursError (EName "a$0$6") (evar "a$0$6" \-> evar "a$0$5"))
  -- y combinator can't type check :(
  , tSynthErr emptyContext ("f" \. ("x" \. var "f" \$ (var "x" \$ var "x")) \$ ("x" \. var "f" \$ (var "x" \$ var "x"))) (OccursError (EName "a$5$14") (evar "a$5$14" \-> evar "a$5$13"))
  -- apply non-function
  , tSynthErr emptyContext (unit \$ unit) (AppliedNonFunction one)
  -- forall shadowing regression tests
  , tCheck (emptyContext |> addVarAnnot "id" ("a" \/. uvar "a" \-> uvar "a")) (var "id" \:: "a" \/. uvar "a" \-> uvar "a") ("a" \/. uvar "a" \-> uvar "a") (emptyContext |> addVarAnnot "id" ("a" \/. uvar "a" \-> uvar "a"))
  , tCheck (emptyContext |> addVarAnnot "id" ("a" \/. uvar "a" \-> uvar "a") |> addUDecl "a") (var "id" \:: "a" \/. uvar "a" \-> uvar "a") ("a" \/. uvar "a" \-> uvar "a") (emptyContext |> addVarAnnot "id" ("a" \/. uvar "a" \-> uvar "a") |> addUDecl "a")
  , tSynthSimple emptyContext (letAnnot "x" one (letAnnot "x" one unit (var "x")) (var "x")) one
  , tSynthSimple emptyContext (letAnnot "x" one (letAnnot "x" tint (int 50) unit) (var "x")) one
  , tSynthErr emptyContext (letAnnot "x" one (letAnnot "x" tint unit (var "x")) (var "x")) (Mismatch tint one)
  , tSynthErr emptyContext (letAnnot "x" one (letAnnot "x" tint (int 100) (var "x")) (var "x")) (Mismatch one tint)
  -- shadowing
  , tSynthSimple emptyContext (elet "x" unit (elet "x" (int 1) (var "x"))) tint
  -- universal scoping an referencing
  , tSynthSimple emptyContext (letAnnot "id" ("a" \/. uvar "a" \-> uvar "a") (lamAnnot "x" (uvar "a") (var "x")) (var "id" \$ unit)) one
  -- tuples
  , tSynthSimple emptyContext (tup [int 1, int 2]) (ttup [tint, tint])
  , tCheck emptyContext (lamAnnot "x" (uvar "a") (tup [var "x", var "x"])) ("a" \/. (uvar "a" \-> ttup [uvar "a", uvar "a"])) emptyContext
  , tSynthSimple emptyContext (tup [id_, int 1]) (ttup ["a" \/. uvar "a" \-> uvar "a", tint])
  -- cases
  , tSynthSimple emptyContext (ecase (int 1) [(pint 1, unit)]) one
  , tSynthSimple emptyContext (ecase (int 1) [(pvar "x", tup [var "x", var "x", unit])]) (ttup [tint, tint, one])
  , tSynthSimple emptyContext (ecase (tup [int 1, unit]) [(ptup [pvar "x", pvar "y"], tup [var "y", var "x", var "x"])]) (ttup [one, tint, tint])
  -- nested tuple pattern
  , tSynthSimple emptyContext (ecase (tup [unit, tup[int 1, unit]]) [(ptup [pwild, ptup [pvar "x", pwild]], tup [var "x", var "x"])]) (ttup [tint, tint])
  , tSynthSimple emptyContext (ecase (tup [unit, tup[int 1, unit]]) [(ptup [pwild `pannot` one, ptup [pvar "x" `pannot` tint, pwild] `pannot` ttup [tint, one]], tup [var "x", var "x"])]) (ttup [tint, tint])
  -- tuple swap
  , let e = ("pair" \. ecase (var "pair") [(ptup [pvar "x", pvar "y"], tup [var "y", var "x"])])
    in tCheck emptyContext e ("a" \/. "b" \/. ttup [uvar "a", uvar "b"] \-> ttup [uvar "b", uvar "a"]) emptyContext
  , tSynthErr emptyContext (ecase (int 1) [(ptup [], unit)]) (Mismatch tint one)
  , tSynthErr emptyContext (ecase (int 1) [(ptup [pvar "x", pvar "y"], var "x")]) (Mismatch tint (ttup [evar "match$3", evar "match$4"]))
  , tSynthErr emptyContext (ecase (tup [unit, unit]) [(pint 1, "x" \. var "x")]) (Mismatch (ttup [one, one]) tint)
    -- pattern match shadow with different types (wf error) TODO make it an or pattern when you make or patterns
  , tSynthErr emptyContext (ecase (tup [int 1, unit]) [(ptup [pvar "x", pvar "x"], unit)]) (Mismatch one tint)
  -- variables across different matches are independent
  , tSynthSimple emptyContext (ecase (tup [int 1, unit]) [(ptup [pvar "x", pvar "y"], tup [var "y", var "x"]), (ptup [pvar "y", pvar "x"], tup [var "x", var "y"])]) (ttup [one, tint])
  -- when there are subtypes in different cases, order doesn't matter and it picks the supertype
  , tSynthSimple emptyContext (ecase unit [(pwild, "x" \. var "x" \:: one \-> one), (pwild, "x" \. var "x" \:: "a" \/. uvar "a" \-> uvar "a")]) (one \-> one)
  , tSynthSimple emptyContext (ecase unit [(pwild, "x" \. var "x" \:: "a" \/. uvar "a" \-> uvar "a"), (pwild, "x" \. var "x" \:: one \-> one)]) (one \-> one)
  -- TODO investigate unbound. try to get it passing with \/a.a after
--  , tSynthSimple emptyContext (ecase unit [(pwild, "x" \. var "x" \:: "a" \/. uvar "a" \-> uvar "a"), (pwild, "x" \. var "x" \:: "a"\/. ("b" \/. uvar "b") \-> uvar "a")]) ("a" \/. uvar "a" \-> uvar "a")
  -- or pattern
  , tSynthSimple emptyContext (ecase (int 1) [(pint 1 \| pint 2 \| pint 3, unit)]) one
  , tSynthSimple emptyContext (ecase (tup [int 1, unit]) [(ptup [pint 1 \| pint 2, pvar "y"], var "y")]) one
  , tSynthSimple emptyContext (ecase (tup [int 1, unit]) [(ptup [pint 1, pvar "y"] \| ptup [pint 2, pvar "y"], var "y")]) one
  , tSynthErr emptyContext (ecase (tup [int 1, unit]) [(ptup [pvar "x", pvar "y"] \| pvar "x", unit)]) (OccursError (EName "match$3") (ttup [evar "match$3", evar "match$4"]))
  , tSynthErr emptyContext (ecase (tup [int 1, unit]) [(ptup [pvar "x", pvar "y"] \| ptup [pvar "y", pvar "x"], unit)]) (Mismatch one tint)
  ]

tests :: Test
tests = TestList
    [ ctxTests
    , subtypeTests
    , synthCheckTests
    ]

main :: IO Counts
main = runTestTT tests
-- TODO test error locations
-- TODO test the forall shadowing more. You are allowing non-well-formed contexts, but it would be unreasonable to
--   expect the user to make unique variables for all of their universal types. Just make sure it can't screw up.
-- TODO test more type errors
