{-
Check constraints given for functions.
-}

module FunctionChecker where

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
import TypesStuff
import StmtChecker

functionChecker :: StateT Env IO ()
functionChecker = do
    (_, _,funs, _) <- get
    names <- return $ M.keys funs
    blocks <- return [ x | (_, _, x) <- M.elems funs]
    functions <- return $ zip names blocks
    execFuns functions

execFuns :: [(Ident, BlockD)] -> StateT Env IO ()
execFuns [] = return ()
execFuns ((name, b@(Block info block)):end) = do
    (vars, d, funs, c) <- get
    (Just (t, args, _)) <- return $ M.lookup name funs
    extendedBlock <- return $ addArguments args block
    wasRet <-  doBlock True initialEnv name False (Block info extendedBlock)
    put(vars, d, funs, c)
    if(wasRet == True || (getType t) == (Void Nothing)) then execFuns end
    else noRetErr info name

addArguments :: [(TypeD, Ident)] -> [Stmt (Maybe (Int, Int))] -> [Stmt (Maybe (Int, Int))]
addArguments [] x = x
addArguments ((t,ident):xs) block = addArguments xs ((Decl Nothing t [(NoInit Nothing ident)]):block)


newFunction :: TopDefD -> StateT Env IO ()
newFunction (FnDef info ret name@(Ident funName) args block) = do
    exists <- checkName False name
    case exists of
        (Just i) -> funDuplErr info funName i
        otherwise -> do
                arguments <- (checkParams args)
                addFun name ret arguments block


addFun :: Ident -> TypeD -> [(TypeD, Ident)] -> BlockD -> StateT Env IO ()
addFun name ret args block = do
    (vars, decls, funs, classes)<- get
    put(vars, decls, M.insert name (ret, args, block) funs, classes)
    return ()


checkParams :: [Arg (Maybe(Int, Int))] -> StateT Env IO [(Type (Maybe(Int, Int)), Ident)]
checkParams args = do
    names <- return $ map (\(Arg a t name)->name) args
    case (findDupArgs names) of
        Nothing -> return $ map (\(Arg a t name)-> (t, name)) args
        (Just duplicate@(Ident var)) -> do
            dups <- return $ take 1 $ reverse $ filter ((\(Arg a t name)-> (name == duplicate))) args
            positions <- return $ head (map (\(Arg a t name) -> a) dups)
            funArgDupl positions var
            return []

findDupArgs :: [Ident] -> Maybe Ident
findDupArgs [] = Nothing
findDupArgs (name:xs) = if (name `elem` xs) then (Just name) else Nothing
