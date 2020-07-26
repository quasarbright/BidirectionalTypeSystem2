module Environment where

import Data.List
import qualified Data.Set as Set
import Common
import Exprs
import Types

-- | An item occurring in a type checking context
data ContextItem a = UDecl String
               | VarAnnot String (Type a)
               | EDecl String
               | EMarker String
               | ESol String (Type a) -- better be mono type
                deriving(Eq)

instance Show (ContextItem a) where
  show item = case item of
      UDecl name -> show (UName name)
      VarAnnot name t -> concat [show (VName name)," :: ",show t]
      EDecl name -> show (EName name)
      EMarker name -> "MARK: "++show (EName name)
      ESol name t -> concat [show (EName name)," = ",show t]


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


emptyContext :: Context a
emptyContext = Context [] 0

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


-- observations


-- | does the context have the given item?
containsItem :: ContextItem a -> Context a -> Bool
containsItem item ctx = item `elem` getItems ctx

-- | does the context have any items with given name? Only checks left-hand-sides.
containsName :: Name -> Context a -> Bool
containsName name ctx = any (itemHasName name) (getItems ctx)

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

-- | Retrieve the set of all names in the domain of this context.
getAllItemNames :: Context a -> Set.Set Name
getAllItemNames ctx =
  getItems ctx
  |> fmap getItemName
  |> Set.fromList

-- | Retrieve the set of all names in the domain of this context.
-- Alias for @getAllItemNames@
domain :: Context a -> Set.Set Name
domain = getAllItemNames

-- | Generate a single unique existential name derived from the given base name.
-- Also returns the same context with a new unique-name-generator state.
getFreshExistentialFrom :: String -> Context a -> (String, Context a)
getFreshExistentialFrom baseName ctx = (concat [baseName,"$",show $ version ctx],ctx{version=version ctx+1})

-- Item removal


-- | remove any context items chronologically after the specified existential marker,
-- excluding the marker from the result.
removeItemsAfterEMarker :: String -> ContextModifier a
removeItemsAfterEMarker = removeItemsAfterItem . EMarker

-- | remove any context items chronologically after the specified universal declaration,
-- excluding the declaration from the result.
removeAfterUDecl :: String -> ContextModifier a
removeAfterUDecl = removeItemsAfterItem . UDecl

-- | remove any context items chronologically after the given one, excluding the given item from the result.
removeItemsAfterItem :: ContextItem a -> ContextModifier a
removeItemsAfterItem item = removeItemsAfterCondition (item ==)

-- | remove any context items chronologically after the first passing of the given predicate.
-- The passing context item will be excluded from the result
removeItemsAfterCondition :: (ContextItem a -> Bool) -> ContextModifier a
removeItemsAfterCondition p = modifyContext $ \items ->
  items
  |> reverse
  |> takeWhile (not . p)
  |> reverse


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

-- | Used in the InstLArr Instantiation rule from the paper:
-- CTX[a?] -> CTX[a2?, a1?, a? = a1? -> a2?].
-- Performs that replacement by generating unique names.
-- Pass in the existential name ("a") and a tag for the created types.
instLArrReplacement :: String -> a -> Context a -> Context a
instLArrReplacement name tag ctx =
  let
      (retName, ctx') = getFreshExistentialFrom name ctx
      (argName, ctx'') = getFreshExistentialFrom name ctx'
  in
  replaceItemWithItems
    (EDecl name)
    [ EDecl retName
    , EDecl argName
    , ESol name (TyArr (EVar argName tag) (EVar retName tag) tag)
    ]
    ctx''