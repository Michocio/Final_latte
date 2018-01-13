{-
Module consists of all possible errors at the frontend surface.
-}

module FrontEndErrors where

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
import System.Exit ( exitFailure, exitSuccess)

import Environment
import TypesStuff
import Misc

frontError :: IO () -> StateT Env IO ()
frontError kind = do
    liftIO kind
    liftIO exitFailure

mainUndeclared :: IO ()
mainUndeclared = liftIO $ putStrLn "Can't find function int main()"

classNameDupErr :: Debug -> Type Debug -> StateT Env IO ()
classNameDupErr info1 info2 = do
        liftIO $ putStrLn $ (show $ fromJust info1) ++
            ": Duplicated name of class " ++ "name" ++
            ", firstly declared at: " ++ (show $ getTypeInfo info2)
        liftIO exitFailure

classFieldDupErr :: Debug -> Type Debug -> Ident -> StateT Env IO ()
classFieldDupErr info1 info2 ident = do
    liftIO $ putStrLn $ (show $ fromJust info1) ++ ": Duplicated name of class's field " ++ (show ident) ++
        ", firstly declared at: " ++ (show $ getTypeInfo info2)
    liftIO $ exitFailure

varUndeclared :: Debug -> Ident -> StateT Env IO (TypeD)
varUndeclared debug (Ident name) = do
    liftIO $ putStrLn $ (show $ fromJust debug) ++ ": variable " ++ (name) ++" doesn't exists"
    liftIO exitFailure

operatorErr :: Bool -> TypeD -> Debug -> StateT Env IO (TypeD)
operatorErr multi type_ debug = do
    if(multi) then
        liftIO $ putStrLn $ (show $ fromJust debug) ++ ": " ++ (show type_) ++  " values needed in that operation"
    else
        liftIO $ putStrLn $ (show $ fromJust debug) ++ ": " ++ (show type_) ++  " value needed in that operation"
    liftIO exitFailure

operatorArbErr ::Debug -> StateT Env IO (TypeD)
operatorArbErr debug = do
            liftIO $ putStrLn $ (show $ fromJust debug) ++ ": " ++ "wrong types for given operator"
            liftIO exitFailure

compError :: Debug -> StateT Env IO (TypeD)
compError debug = do
    liftIO $ putStrLn $ (show $ fromJust debug) ++ ": Comparision between unmatching types"
    liftIO exitFailure

funUndeclared :: Debug -> String -> StateT Env IO (TypeD)
funUndeclared info name = do
    liftIO $ putStrLn $ (show $ fromJust info) ++ ": function " ++ name ++ "doesn't exists"
    liftIO exitFailure

funArgDupl :: Debug -> String -> StateT Env IO [(Type (Maybe(Int, Int)), Ident)]
funArgDupl info var = do
    liftIO $ putStrLn $ (show $ fromJust info) ++ ": Duplicated name of argument " ++ (var)
    liftIO $ exitFailure

funDuplErr :: Debug -> String -> TypeD -> StateT Env IO ()
funDuplErr info fun i = do
    liftIO $ putStrLn $ (show $ fromJust info) ++ ": Duplicated name of function " ++ fun ++
        ", firstly declared at: " ++ (show $ getTypeInfo i)
    liftIO exitFailure

numberOfArgsErr :: Debug -> String -> StateT Env IO (TypeD)
numberOfArgsErr info name = do
    liftIO $ putStrLn $ (show  $ fromJust info) ++ ": Wrong number of arguments given for " ++ name
    liftIO exitFailure

typesOfArgsErr :: Debug -> String -> StateT Env IO (TypeD)
typesOfArgsErr info name = do
    liftIO $ putStrLn $ (show  $ fromJust info) ++ ": Wrong types of arguments given for function " ++ name
    liftIO exitFailure

notArray :: (Int, Int) -> Ident -> StateT Env IO (TypeD)
notArray info (Ident name) = do
    liftIO $ putStrLn $ (show info) ++ ": not an array " ++ name
    liftIO exitFailure

nonVoidRetErr :: Maybe (Int, Int) ->String -> TypeD -> TypeD ->  StateT Env IO (Bool)
nonVoidRetErr info name desiredType a = do
    liftIO $ putStrLn $ (show $ fromJust info) ++ ": wrong return type in function " ++
        name ++ ", expected " ++ (printType (getType desiredType)) ++ " but given " ++
        (printType (getType a))
    liftIO exitFailure

noRetErr :: Debug -> Ident -> StateT Env IO ()
noRetErr info (Ident name) = do
    liftIO $ putStrLn $ (show info) ++ ": Non void function " ++ (name) ++ " may not return any value."
    liftIO exitFailure

retErr :: Debug -> String ->  StateT Env IO (Bool)
retErr info name = do
    liftIO $ putStrLn $ (show $ fromJust info) ++ ": wrong return type in not void function " ++
        name
    liftIO exitFailure

ifCondErr :: Debug -> StateT Env IO (Bool)
ifCondErr info = do
    liftIO $ putStrLn $ (show $ fromJust info) ++
        ": expected bool expression as condition Wrong expression in if condition"
    liftIO exitFailure

wrongTypeAss :: Debug -> StateT Env IO (Bool)
wrongTypeAss info = do
        liftIO $ putStrLn $ (show $ fromJust info) ++ ": wrong type of value to assign"
        liftIO exitFailure

varRedeclaration :: Debug -> Ident -> StateT Env IO ()
varRedeclaration info (Ident name) =   do
    liftIO $ putStrLn $ (show $ fromJust info) ++ ": Redeclaration of previously declared variable: "
        ++ (name)
    liftIO exitFailure
