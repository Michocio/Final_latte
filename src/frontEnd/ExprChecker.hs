{-
Checks if expressions are correct.
-}

module ExprChecker where

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

exprType :: Expr (Maybe (Int, Int)) -> StateT Env IO (TypeD)
exprType exp = case exp of
    EVar a lvalue -> do
        vars <- getVars
        (arr, name) <- return (identLValue lvalue)
        case (M.lookup name vars) of
            (Just x) -> do
                if(arr && (isArray x == False)) then notArray (getTypeInfo x) name
                else do
                    if(arr) then return $ arrayType x
                    else return $ getType x
            otherwise -> varUndeclared a name
    ENewArr a type_ expr -> do
        return $ Array a type_
    EArrLen a name -> do
        vars <- getVars
        case (M.lookup name vars) of
            (Just x) -> do
                if(isArray x == False) then notArray (getTypeInfo x) name
                else return (Int Nothing)
            otherwise -> varUndeclared a name
    --ENullCast a type_ -> ENullCast (f a) (fmap f type_)
    ELitInt a integer -> return (Int a)
    ELitTrue a -> return (Bool a)
    ELitFalse a -> return (Bool a)
    EString a string -> return (Str a)
    exp@(EApp a ident exprs) -> checkFunCall exp
    --EClApp a ident1 ident2 exprs -> EClApp (f a) ident1 ident2 (map (fmap f) exprs)
    Neg a expr -> do
        expT <- ifInt expr
        if (expT) then return (Int a) else operatorErr False (Int Nothing) a
    Not a expr ->  do
        expT <- ifBool expr
        if (expT) then return (Bool a) else operatorErr False (Bool Nothing) a
    EMul a expr1 mulop expr2 -> do
        exp1 <- ifInt expr1
        exp2 <- ifInt expr2
        if (exp1 && exp2) then return (Int a) else operatorErr True (Int Nothing) a
        return (Int a)
    EAdd a expr1 addop expr2 -> do
        exp1 <- ifInt expr1
        exp2 <- ifInt expr2
        if (exp1 && exp2) then return (Int a) else do
            exp1_ <- ifStr expr1
            exp2_ <- ifStr expr2
            if (exp1_ && exp2_) then return (Str a) else operatorArbErr a
    ERel a expr1 (EQU t) expr2 -> do
        exp1 <- exprType expr1
        exp2 <- exprType expr2
        if((getType exp1) /= (getType exp2)) then compError a
        else
            return (Bool a)
    ERel a expr1 (NE t) expr2 -> exprType (ERel a expr1 (EQU t) expr2)
    ERel a expr1 _ expr2 -> do
        exp1 <- ifInt expr1
        exp2 <- ifInt expr2
        if (exp1 && exp2) then return (Int a) else operatorErr True (Int Nothing) a
        return (Bool a)
    EAnd a expr1 expr2 -> do
        exp1 <- ifBool expr1
        exp2 <- ifBool expr2
        if (exp1 && exp2) then return (Bool a) else operatorErr True (Bool Nothing) a
        return (Bool a)
    EOr a expr1 expr2 ->  exprType (EAnd a expr1 expr2)


checkFunCall :: Expr (Maybe (Int, Int)) -> StateT Env IO (TypeD)
checkFunCall (EApp info ident@(Ident name) exprs) = do
    funs <- getFuns
    case (M.lookup ident funs) of
        (Just (tFun, args, _)) -> do
            (types, _) <- return $ unzip args
            unwrapTypes <- return $ map getType types
            givenTypes <-  mapM (exprType) exprs
            types <- return $ map getType givenTypes
            if(length types /= length unwrapTypes) then numberOfArgsErr info name
            else do
                if (types == unwrapTypes) then return tFun
                else  typesOfArgsErr info name
        otherwise -> funUndeclared info name


ifInt :: Expr (Maybe (Int, Int)) -> StateT Env IO (Bool)
ifInt exp = do
    expT <- exprType exp
    return (getType expT == (Int Nothing))

ifStr :: Expr (Maybe (Int, Int)) -> StateT Env IO (Bool)
ifStr exp = do
    expT <- exprType exp
    return (getType expT == (Str Nothing))

ifBool :: Expr (Maybe (Int, Int)) -> StateT Env IO (Bool)
ifBool exp = do
    expT <- exprType exp
    return (getType expT == (Bool Nothing))
