module Decls where

import Common
import Types
import Control.Monad
import Data.List


data Decl a =
    -- | data definition
    DataDecl String [String] [(String, [Type a])] a

instance Show (Decl a) where
    show (DataDecl tName uNames conDecls _) = concat ["data ",tName," ", unwords uNames," = ",conDeclsStr]
        where
            conDeclsStr =
                conDecls
                -- | just render it as if it was a type application
                |> fmap (\ ~(cName, tys) -> foldl tapp (tcon cName) (void <$> tys))
                |> fmap show
                |> intercalate " | "

instance Eq (Decl a) where
    DataDecl tName uNames conDecls _ == DataDecl tName' uNames' conDecls' _ = (tName, uNames, conDecls) == (tName', uNames', conDecls')

instance Functor Decl where
    fmap f (DataDecl tName uNames conDecls a) = DataDecl tName uNames conDecls' (f a)
        where
            conDecls' =
                conDecls
                |> fmap (\ ~(cName, tys) -> (cName, fmap f <$> tys))

instance Tagged Decl where
    getTag (DataDecl _ _ _ a) = a

    setTag a (DataDecl x y z _) = DataDecl x y z a