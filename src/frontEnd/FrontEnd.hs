{-
Main module responsible for checking corretness of fronend surface.
-}

module FrontEnd where

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

import Environment
import FrontEndErrors
import FunctionChecker
import TypesStuff

import ClassChecker
import ExprChecker
import IntermediateCode
import StmtChecker

-- Main functions
frontEnd :: ProgramD -> IO ()
frontEnd p =  (liftIO $ evalStateT (checkProgram p) initialEnv)

checkProgram :: ProgramD -> StateT Env IO ()
checkProgram  (Program info []) = return ()
checkProgram  (Program info (x:xs)) = checkTopDef (x:xs)

checkTopDef :: [TopDefD] -> StateT Env IO ()
checkTopDef [] = do
    mainExists <- checkName False (Ident "main")
    case (mainExists) of
        Nothing -> frontError mainUndeclared
        otherwise -> do
            (_, _,funs, _) <- get
            case (fromJust $ M.lookup (Ident "main") funs) of
                (Int info, [], _) -> do
                    classChecker
                    functionChecker
                    methodChecker
                    return ()
                otherwise -> frontError mainUndeclared

checkTopDef (x:xs) = do
    doTopDef x
    checkTopDef xs

doTopDef :: TopDefD -> StateT Env IO ()
doTopDef fun@(FnDef a type_ ident args block) = newFunction fun
doTopDef class_@(ClassDef a classheader classblock) = newClass class_
