module Environment where

import Common
import Exprs
import Types
import qualified Data.Set as Set

-- | An item occurring in a type checking context
data ContextItem a = UDecl String
               | VarAnnot String (Type a)
               | EDecl String
               | EMarker String
               | ESol String (Type a) -- better be mono type
                deriving(Eq)
-- | an ordered context for type checking.
-- items are chronologically backwards. The first item is the most recent
newtype Context a = Context{ getItems :: [ContextItem a] }

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

-- Item removal

-- | remove any context items chronologically after the specified existential marker,
-- excluding the marker from the result.
removeItemsAfterEMarker :: String -> Context a -> Context a
removeItemsAfterEMarker = removeItemsAfterItem . EMarker

-- | remove any context items chronologically after the specified universal declaration,
-- excluding the declaration from the result.
removeAfterUDecl :: String -> Context a -> Context a
removeAfterUDecl = removeItemsAfterItem . UDecl

-- | remove any context items chronologically after the given one, excluding the given item from the result.
removeItemsAfterItem :: ContextItem a -> Context a -> Context a
removeItemsAfterItem item = removeItemsAfterCondition (item ==)

-- | remove any context items chronologically after the first passing of the given predicate.
-- The passing context item will be excluded from the result
removeItemsAfterCondition :: (ContextItem a -> Bool) -> Context a -> Context a
removeItemsAfterCondition p ctx =
  getItems ctx
  |> reverse
  |> takeWhile (not . p)
  |> reverse
  |> Context