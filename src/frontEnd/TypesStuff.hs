{-
Heloing functions for operating on types.
-}
module TypesStuff where

import Control.Monad.Writer
import Control.Monad.Writer.Lazy
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative

import qualified Data.Map as M
import Data.Char
import LexGrammar
import ParGrammar
import SkelGrammar
import PrintGrammar
import AbsGrammar
import ErrM
import Data.Typeable
import Control.Exception
import Control.Monad.Trans.Maybe
import Control.Monad.Identity
import Data.List
import Data.Maybe
import System.Exit ( exitFailure, exitSuccess )

import Misc

getTypeInfo :: Type (Maybe (Int, Int)) -> (Int, Int)
getTypeInfo x = case x of
    CustomType (Just a) ident -> a
    Int (Just a) -> a
    Str (Just a) -> a
    Bool (Just a) -> a
    Void (Just a) -> a
    Array (Just a) type_ -> a

hashType :: Type (Maybe (Int, Int)) -> String
hashType x = case x of
    CustomType _ ident -> (show ident)
    Int _ -> "int"
    Str _  -> "str"
    Bool _ -> "bool"
    Void _ -> "void"
    Array _ type_ -> hashType type_ ++ "[]"

getType :: Type (Maybe (Int, Int)) -> Type (Maybe (Int, Int))
getType x = case x of
    CustomType _ ident -> CustomType Nothing ident
    Int _ -> Int Nothing
    Str _  -> Str Nothing
    Bool _ -> Bool Nothing
    Void _ -> Void Nothing
    Array _ type_ -> Array Nothing (getType type_)

isArray :: Type (Maybe (Int, Int)) -> Bool
isArray (Array _ type_) = True
isArray _ = False

arrayType ::  Type (Maybe (Int, Int)) -> Type (Maybe (Int, Int))
arrayType (Array _ type_) = type_

identLValue :: LValue a -> (Bool, Ident)
identLValue (ValVar a name) = (False, name)
identLValue (ValArr a name e) = (True, name)
identLValue (ValField a obj field) = (False, snd $ identLValue obj)


stringLValue :: LValue a -> (Bool, String)
stringLValue (ValVar a (Ident name)) = (False, name)
stringLValue (ValArr a (Ident name) e) = (True, name)
stringLValue (ValField a obj field) = (False, "class")

getIndex :: LValue a -> Expr a
getIndex (ValArr a name e) = e

equalTypes :: Type Debug -> Type Debug -> Bool
equalTypes t1 t2 = (getType t1) == (getType t2)
