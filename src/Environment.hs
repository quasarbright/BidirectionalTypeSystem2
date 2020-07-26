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
-- items are chronologically backwards. The first item is the most recent
newtype Context a = Context{ getItems :: [ContextItem a] } deriving(Eq)

instance Show (Context a) where
    show ctx =
      getItems ctx
      |> reverse
      |> fmap show
      |> intercalate "\n"
      |> \s -> concat ["{",s,"}"]

-- utility

modifyContext :: ([ContextItem a] -> [ContextItem a]) -> Context a -> Context a
modifyContext f ctx = Context{getItems=f (getItems ctx)}


-- construction


emptyContext :: Context a
emptyContext = Context []

-- | Add the given context item to the context (the item will be chronologically last)
addItem :: ContextItem a -> Context a -> Context a
addItem item = modifyContext (item:)

-- | declare a universal variable
addUDecl :: String -> Context a -> Context a
addUDecl = addItem . UDecl

-- | declare an existential variable
addEDecl :: String -> Context a -> Context a
addEDecl = addItem . EDecl

-- | add an existential variable marker
addEMarker :: String -> Context a -> Context a
addEMarker = addItem . EMarker

-- | add an existential solution to the environment. NOTE: does not replace a decl with a solution, just blindly adds it.
addESol :: String -> Type a -> Context a -> Context a
addESol name t = addItem (ESol name t)

-- | add a variable (expr) annotation to the environment
addVarAnnot :: String -> Type a -> Context a -> Context a
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
removeItemsAfterCondition p = modifyContext $ \items ->
  items
  |> reverse
  |> takeWhile (not . p)
  |> reverse
