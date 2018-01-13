{-
Statements correctness.
-}
module StmtChecker where

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
import ExprChecker
import TypesStuff
import Misc

doBlock :: Bool-> Env -> Ident -> Bool -> BlockD -> StateT Env IO Bool
doBlock True env f ret block = do
    (vars, decls, funs, cl) <- get
    put(vars, M.empty, funs, cl)
    doBlock False (vars, decls, funs, cl) f ret block
doBlock start env _ ret (Block _ []) = do
        put env
        return ret
doBlock start env funName ret (Block a (x:xs)) = do
    newRet <- runStmt funName x
    if(ret == False) then doBlock False env funName newRet (Block a xs)
        else doBlock False env funName ret (Block a xs)

runStmt :: Ident -> Stmt (Maybe(Int, Int)) -> StateT Env IO Bool
runStmt funName@(Ident name) (Ret info expr) = do
    a <- exprType expr
    funs <- getFuns
    (desiredType, _, _) <- return $ fromJust $ M.lookup funName funs
    if((getType desiredType) == (getType a)) then return True
        else nonVoidRetErr info name desiredType a
runStmt funName@(Ident name) (VRet info) = do
    funs <- getFuns
    (desiredType, _, _) <- return $ fromJust $ M.lookup funName funs
    if(getType desiredType == (Void Nothing)) then return True
        else retErr info name
runStmt funName@(Ident name) (Empty a) = return False
runStmt funName@(Ident name) (Cond info cond ifBlock) = do
    condType <- exprType cond
    if((getType condType) == (Bool Nothing)) then do
        runStmt funName (BStmt Nothing $ Block Nothing [ifBlock])
        if(isTrivial cond == (True, True)) then return True
        else return False
    else ifCondErr info
runStmt funName@(Ident name) (CondElse info cond ifBlock elseBlock) = do
    condType <- exprType cond
    if((getType condType) == (Bool Nothing)) then do
        ifRet <- runStmt funName  (BStmt Nothing $ Block Nothing [ifBlock])
        elseRet <- runStmt funName (BStmt Nothing $ Block Nothing [elseBlock])
        if(isTrivial cond == (True, True) && (True == ifRet)) then return True
        else do
            if(isTrivial cond == (True, False) && (True == elseRet)) then return True
            else return ((True == ifRet) == elseRet)
    else ifCondErr info
runStmt funName@(Ident name) (While a cond block) = do
    runStmt funName (Cond a cond block)
runStmt _ (SExp a expr) = do
    exprType expr
    return False
runStmt _ (Decl a vType items) = do
    x <- mapM (itemOperator vType) items
    return False
runStmt _ (Ass a lvalue expr) = do
    lType <- exprType (EVar a lvalue)
    rType <- exprType expr
    if((getType lType) /=  getType rType) then wrongTypeAss a
    else return False
runStmt fun (BStmt a block) = do
    doBlock True initialEnv fun False block
runStmt _ (Incr a lvalue) = do
    varType <- exprType (EVar a lvalue)
    if(getType varType /= (Int Nothing)) then do
        x <- operatorErr False (Int Nothing) a
        return False
    else return False
runStmt x (Decr a lvalue) = runStmt x (Incr a lvalue)
runStmt _ _ = return False

isTrivial :: Expr Debug -> (Bool, Bool)
isTrivial (ELitTrue _) = (True, True)
isTrivial (ELitFalse _) = (True, False)
isTrivial _ = (False, False)

itemOperator :: TypeD -> Item (Maybe (Int, Int))-> StateT Env IO ()
itemOperator t (NoInit info name) = do
    (vars, decls, funs, classes) <- get
    case (M.lookup name decls) of
        (Just x) -> varRedeclaration info name
        (otherwise) -> do
            put (M.insert name t vars, M.insert name t decls, funs, classes)
            return ()

itemOperator t (Init info name expr) = do
    expType <- exprType expr
    if((getType t) /= (getType $ expType)) then do
        err <- wrongTypeAss info
        return ()
    else itemOperator t (NoInit info name)
