module Environment where

import Data.List
import qualified Data.Set as Set
import Control.Monad
import Common
import Types

-- former to do: think about a context [x :: \/a.a->a,  y :: \/a.a->a->a,  decl a] or something similar
-- Thought about it, couldn't cause an error like "expected a, got a" in haskell, so I should be fine.

-- | An item occurring in a type checking context
data ContextItem a = UDecl String
               | VarAnnot String (Type a)
               | EDecl String
               | EMarker String
               | ESol String (Type a) -- better be mono type
               | ConAnnot String (Type a)
               | TAnnot String (Kind a)
                deriving(Eq)

instance Show (ContextItem a) where
  show item = case item of
      UDecl name -> show (UName name)
      VarAnnot name t -> concat [show (VName name)," :: ",show t]
      EDecl name -> show (EName name)
      EMarker name -> "MARK: "++show (EName name)
      ESol name t -> concat [show (EName name)," = ",show t]
      ConAnnot name t -> concat [show (CName name)," :: ",show t]
      TAnnot name kind -> concat [show (DName name)," :: ", show kind]

-- | an ordered context for type checking.
-- items are chronologically backwards. The first item is the most recent.
-- Has a version number incremented every modification / existential generation. Used to generate unique names.
data Context a = Context{ getItems :: [ContextItem a], version :: Int }

instance Eq (Context a) where
  ctx == ctx' = getItems ctx == getItems ctx'

instance Show (Context a) where
    show ctx =
      getItems ctx
      |> reverse
      |> fmap show
      |> intercalate "\n"
      |> \s -> concat ["{",s,"}v=",show (version ctx)]

-- | type alias to save me time writing signatures
type ContextModifier a = Context a -> Context a


-- utility

-- | Utility for lifting list functions to context functions.
-- Increments version.
modifyContext :: ([ContextItem a] -> [ContextItem a]) -> ContextModifier a
modifyContext f ctx = Context{getItems=f (getItems ctx), version=version ctx + 1}


-- construction

-- | Construct a context from the given list of context items.
-- items should be in reverse chronological order!!!
fromList :: [ContextItem a] -> Context a
fromList items = Context{ getItems = items, version = length items }

-- | context with no items (version=0)
emptyContext :: Context a
emptyContext = Context{ getItems = [], version = 0 }

-- | Add the given context item to the context (the item will be chronologically last)
addItem :: ContextItem a -> ContextModifier a
addItem item = modifyContext (item:)

-- | declare a universal variable
addUDecl :: String -> ContextModifier a
addUDecl = addItem . UDecl

-- | declare an existential variable
addEDecl :: String -> ContextModifier a
addEDecl = addItem . EDecl

-- | add an existential variable marker
addEMarker :: String -> ContextModifier a
addEMarker = addItem . EMarker

-- | add an existential solution to the environment.
-- NOTE: does not replace a decl with a solution, just blindly adds it.
-- For the replacement, use @recordESol@
addESol :: String -> Type a -> ContextModifier a
addESol name t = addItem (ESol name t)

-- | add a variable (expr) annotation to the environment
addVarAnnot :: String -> Type a -> ContextModifier a
addVarAnnot name t = addItem (VarAnnot name t)

-- | add a (value) constructor annotation to the environment
addConAnnot :: String -> Type a -> ContextModifier a
addConAnnot name t = addItem (ConAnnot name t)

-- | add a type annotation (for a type constructor)
addTAnnot :: String -> Kind a -> ContextModifier a
addTAnnot name kind = addItem (TAnnot name kind)


-- observations


-- | does the context have the given item?
containsItem :: ContextItem a -> Context a -> Bool
containsItem item ctx = item `elem` getItems ctx

-- | does the context have an item which passes the given predicate?
containsItemBy :: (ContextItem a -> Bool) -> Context a -> Bool
containsItemBy p = any p . getItems

-- | does the context have any items with given name? Only checks left-hand-sides. Doesn't ignore markers
containsName :: Name -> Context a -> Bool
containsName name ctx = name `elem` getAllItemNames ctx

-- | does the domain of this context have any items with the given name?
-- Ignores markers.
containsNameInDomain :: Name -> Context a -> Bool
containsNameInDomain name ctx = name `elem` domain ctx

-- | does the context item have the given name? Only checks left-hand-sides
itemHasName :: Name -> ContextItem a -> Bool
itemHasName name item = getItemName item == name

-- | get the name of the given context item
getItemName :: ContextItem a -> Name
getItemName item = case item of
  UDecl name -> UName name
  VarAnnot name _ -> VName name
  EDecl name -> EName name
  EMarker name -> EName name
  ESol name _ -> EName name
  ConAnnot name _ -> CName name
  TAnnot name _ -> DName name

-- | Retrieve the set of all names in this context, including those specified by markers.
getAllItemNames :: Context a -> Set.Set Name
getAllItemNames ctx =
  getItems ctx
  |> fmap getItemName
  |> Set.fromList

-- | Retrieve the set of all names in the domain of this context, ignoring markers.
domain :: Context a -> Set.Set Name
domain ctx =
  getItems ctx
  |> filter (not . isMarker)
  |> fmap getItemName
  |> Set.fromList
  where
    isMarker EMarker{} = True
    isMarker _ = False

-- | Generates a single unique name derived from the given base name.
-- Also returns the same context with a new unique-name-generator state.
getFreshNameFrom :: String -> Context a -> (String, Context a)
getFreshNameFrom baseName ctx = (concat [baseName,"$",show $ version ctx],ctx{version=version ctx+1})

-- | Generates a specified number of unique names derived from the given base name.
-- Also returns the same context with a new unique-name-generator state.
getFreshNamesFrom :: String -> Int -> Context a -> ([String], Context a)
getFreshNamesFrom baseName n ctx = foldl go ([], ctx) [1..n]
  where
    go (names, ctx') _ = (names++[name], ctx'')
      where
        (name, ctx'') = getFreshNameFrom baseName ctx'

-- | find an item which satisfies the given predicate (chronologically last)
findItem :: (ContextItem a -> Bool) -> Context a -> Maybe (ContextItem a)
findItem p = find p . getItems

-- | find an item with the given name (chronologically last)
findItemWithName :: Name -> Context a -> Maybe (ContextItem a)
findItemWithName name = findItem (\item -> getItemName item == name)

-- | Which EDecl occurs (chronologically) last in the context?
whichEDeclLast :: String -> String -> Context a -> Maybe String
whichEDeclLast a b ctx =
  case findItem (\item -> item `elem` [EDecl a, EDecl b]) ctx of
    Just (EDecl name) -> Just name
    Nothing -> Nothing
    Just unexpected -> error ("found unexpected item searching for last edecl: "++show unexpected)

-- | find the type of the variable in the given context
lookupVar :: String -> Context a -> Maybe (Type a)
lookupVar name ctx = do
  item <- findItemWithName (VName name) ctx
  case item of
    VarAnnot _ t -> return t
    _ -> error "found non-var annot when looking up variable's type"

-- | find the type of a value constructor in the given context
lookupCon :: String -> Context a -> Maybe (Type a)
lookupCon name ctx = do
    item <- findItemWithName (CName name) ctx
    case item of
        ConAnnot _ t -> return t
        _ -> error "found non-con annot when looking up a constructor's type"

-- | find the kind of a type constructor in the given context
lookupType :: String -> Context a -> Maybe (Kind a)
lookupType name ctx = do
    item <- findItemWithName (DName name) ctx
    case item of
        TAnnot _ k -> return k
        _ -> error "found non-type annot when looking up a type's kind"


-- Item removal


-- | remove any context items chronologically after the (last) specified existential marker,
-- excluding the marker from the result.
removeItemsAfterEMarker :: String -> ContextModifier a
removeItemsAfterEMarker = removeItemsAfterItem . EMarker

-- | remove any context items chronologically after the (last) specified universal declaration,
-- excluding the declaration from the result.
removeItemsAfterUDecl :: String -> ContextModifier a
removeItemsAfterUDecl = removeItemsAfterItem . UDecl

-- | remove any context items chronologically after the (last) specified variable's annotation,
-- excluding the variable annotation from the result
removeItemsAfterVarAnnot :: String -> Type a -> ContextModifier a
removeItemsAfterVarAnnot x t = removeItemsAfterItem (VarAnnot x t)

-- | remove any context items chronologically after the given one, excluding the given item from the result.
removeItemsAfterItem :: ContextItem a -> ContextModifier a
removeItemsAfterItem item = removeItemsAfterCondition (item ==)

-- | remove any context items chronologically after the last passing of the given predicate.
-- The passing context item will be excluded from the result
removeItemsAfterCondition :: (ContextItem a -> Bool) -> ContextModifier a
removeItemsAfterCondition p = modifyContext $ \items ->
  items
  |> dropWhile (not .p)
  |> safeTail
  where
    safeTail [] = []
    safeTail (_:xs) = xs


-- item replacement


-- | @replaceItem target replacement@ replaces all occurrences of @target@ with @replacement@ in the environment.
-- There should only ever be one of any context item in a context, so this should just do one replacement.
replaceItem :: ContextItem a -> ContextItem a -> ContextModifier a
replaceItem target replacement = modifyContext (fmap (\item -> if item == target then replacement else item))

-- | Changes all declarations of an existential variable to the provided solution.
-- There should only ever be one declaration of the same existential, however.
recordESol :: String -> Type a -> ContextModifier a
recordESol name t = replaceItem (EDecl name) (ESol name t)

-- | @replaceItemWithItems target replacements@ replaces all occurrences of @target@ with @replacements@ in the environment.
-- @replacements@ should be in chronological order.
-- There should only ever be one of any context item in a context, so this should just do one replacement.
replaceItemWithItems :: ContextItem a -> [ContextItem a] -> ContextModifier a
replaceItemWithItems target replacements = modifyContext $ \items ->
  items
  |> fmap (\item -> if item == target then reverse replacements else [item])
  |> concat

-- | Used in the InstLArr and InstRArr Instantiation rules from the paper:
-- CTX[a?] -> CTX[a2?, a1?, a? = a1? -> a2?].
-- Performs that replacement by generating fresh existentials 
-- and returns the names of the arg and ret type existentials.
-- Pass in the existential name ("a") and a tag for the created types.
instArrReplacement :: String -> a -> Context a -> (String, String, Context a)
instArrReplacement name tag ctx =
  let ~([retName, argName], ctx') = getFreshNamesFrom name 2 ctx in
  let target = EDecl name in
  let replacements = [EDecl retName, EDecl argName, ESol name (TyArr (EVar argName tag) (EVar retName tag) tag)] in
  let finalCtx = replaceItemWithItems target replacements ctx' in
  (argName, retName, finalCtx)

-- | Used in the InstLTup and InstRTup instantiation rules from the paper:
-- CTX[a?] -> CTX[an, ..., a1, a=(a1, ..., an)]
-- Performs that replacement by generating fresh existentials 
-- and returns the names of the tuple subtype existentials.
-- Pass in the existential name ("a") and a tag for the created types.
instTupReplacement :: String -> Int -> a -> Context a -> ([String], Context a)
instTupReplacement name n tag = abstractReplacement (`TyTup` tag) name n tag

-- | Used in InstLDelta and InstRDelta instantiation rules
-- CTX[a?] -> CTX[an, ..., a1, a=C a1 ... an]
-- Performs that replacement by generating fresh existentials
-- and returns the names of the application subtype existentials.
-- Pass in the constructor name, the existential name ("a"), and a tag for the created types.
instAppReplacement :: String -> String -> Int -> a -> Context a -> ([String], Context a)
instAppReplacement con name n tag = abstractReplacement (foldl (\ f x -> TyApp f x tag) (TyCon con tag)) name n tag

abstractReplacement :: ([Type a] -> Type a) -> String -> Int -> a -> Context a -> ([String], Context a)
abstractReplacement makeType name n tag ctx =
    let ~(eNames, ctx') = getFreshNamesFrom name n ctx in
    let target = EDecl name in
    let replacements = reverse (EDecl <$> eNames) ++ [ESol name (makeType [EVar eName tag | eName <- eNames])] in
    let finalCtx = replaceItemWithItems target replacements ctx' in
    (eNames, finalCtx)


-- context as a type substitution


contextAsSubstitution :: Context a -> Type a -> Type a
contextAsSubstitution ctx t =
  let recurse = contextAsSubstitution ctx in
  case t of
    TInt{} -> t
    UVar{} -> t -- assumes well-formedness
    EVar name _ ->
      case findItemWithName (EName name) ctx of
        Just (ESol _ t') -> recurse t'
        Just EDecl{} -> t -- assumes well-formedness
        mi -> error ("unexpected item: "++show mi)
    TyScheme name' body tag -> TyScheme name' (recurse body) tag
    TyArr arg ret tag -> TyArr (recurse arg) (recurse ret) tag
    TyTup tys tag -> TyTup (recurse <$> tys) tag
    TyCon{} -> t
    TyApp f x tag -> TyApp (recurse f) (recurse x) tag


-- well-formedness


data ContextWFError a = UnboundUVar String a
                      | UnboundEVar String a
                      | UnboundTCon String a
                      | DupVar (ContextItem a)
                      | DupUVar (ContextItem a)
                      | DupEVar (ContextItem a)
                      | DupEMarker (ContextItem a)
                      | DupCon (ContextItem a)
                      | DupTCon (ContextItem a)
                      deriving(Eq, Show) -- TODO manual Show instance

-- TODO return list of errors instead
-- | check the well-formedness of a type in the given context
checkTypeWellFormedness :: Context a -> Type a -> Either (ContextWFError a) ()
checkTypeWellFormedness ctx t =
  let
    -- | passes if the item is either an EDecl or ESol for the given name, but not a marker
    ePredicate _ EMarker{} = False
    ePredicate name item = itemHasName (EName name) item
  in
  case t of
    TInt{} -> Right ()
    UVar name tag
      | containsItem (UDecl name) ctx -> Right ()
      | otherwise -> Left (UnboundUVar name tag)
    EVar name tag
      | containsItemBy (ePredicate name) ctx -> Right ()
      | otherwise -> Left (UnboundEVar name tag)
    TyScheme name body _ -> checkTypeWellFormedness (addUDecl name ctx) body
    TyArr arg ret _ -> sequence_ (checkTypeWellFormedness ctx <$> [arg, ret])
    TyTup tys _ -> sequence_ (checkTypeWellFormedness ctx <$> tys)
    TyCon name tag
        | DName name `elem` domain ctx -> Right ()
        | otherwise -> Left (UnboundTCon name tag)
    TyApp f x _ -> sequence_ (checkTypeWellFormedness ctx <$> [f, x])

-- | check the well-formedness of a context
checkContextWellFormedness :: Context a -> Either (ContextWFError a) ()
checkContextWellFormedness (Context [] _) = Right ()
checkContextWellFormedness (Context (item:items) v) =
  do
    let ctx = Context items v
    let checkDup onDup item' = when (containsNameInDomain (getItemName item') ctx) (Left $ onDup item')
    case item of
      VarAnnot _ t -> do
        checkDup DupVar item
        checkTypeWellFormedness ctx t
      UDecl{} -> checkDup DupUVar item
      EDecl{} -> checkDup DupEVar item
      ESol _ t -> do
        checkDup DupEVar item
        checkTypeWellFormedness ctx t
      EMarker{} -> do
        when (item `elem` items) (Left $ DupEMarker item)
        checkDup DupEVar item
      ConAnnot _ t -> do
        checkDup DupCon item
        checkTypeWellFormedness ctx t
      TAnnot{} -> do
        checkDup DupTCon item
    checkContextWellFormedness ctx