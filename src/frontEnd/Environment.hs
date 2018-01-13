{-
Common file for all frontend' files.
It defines and controls everything connected with nvironment.
-}

module Environment where
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
import TypesStuff

-- return type, parameters list, fun body
type FunDef = (TypeD, [(TypeD, Ident)], BlockD)

printIntDef = ((Void Nothing), [((Int Nothing), Ident "x")], Block Nothing []);
printStringDef = ((Void Nothing), [((Str Nothing, Ident "x"))], Block Nothing []);
errorDef = ((Void Nothing), [], Block Nothing []);
readIntDef = ((Int Nothing), [], Block Nothing [Ret Nothing (ELitInt Nothing 0)]);
readStringDef = ((Str Nothing), [], Block Nothing [Ret Nothing ( EString Nothing "")]);

predefinied = [(Ident "printInt", printIntDef),
                (Ident "printString", printStringDef),
                (Ident "error", errorDef),
                (Ident "readInt", readIntDef),
                (Ident "readString", readStringDef)]

type ClassField =  M.Map Ident TypeD
type ClassMethod =  M.Map Ident FunDef
type ClassEnv = (ClassField, ClassMethod, Maybe Ident)

--type EEnv = M.Map Ident Bool
type FEnv = M.Map Ident FunDef
type VEnv = M.Map Ident TypeD
type DEnv = M.Map Ident TypeD
type CEnv = M.Map Ident ClassEnv

type Env = (VEnv, DEnv, FEnv, CEnv)

type ProgramD = Program (Maybe (Int, Int))
type TopDefD = TopDef (Maybe (Int, Int))
type TypeD = Type (Maybe (Int, Int))
type BlockD = Block (Maybe (Int, Int))

initialEnv = (M.empty, M.empty, M.fromList predefinied, M.empty)

printType ::  TypeD -> String
printType (Int x) = "int"
printType (Str x) = "string"
printType (Bool x) = "boolean"
printType (Void x) = "void"
printType x = show x

getTypeOfFun :: Ident ->  StateT Env IO (Maybe TypeD)
getTypeOfFun name = do
    (_, _,funs, _) <- get
    case (M.lookup name funs) of
        (Just (t, _, _)) -> return $ Just t
        otherwise -> return Nothing

checkName :: Bool -> Ident -> StateT Env IO (Maybe TypeD)
checkName ifClass name = do
    if(ifClass) then do
        (_, _, _, look) <- get
        case (M.lookup name look) of
            (Just (_, _, _)) -> return $ Just (Int Nothing)
            otherwise -> return Nothing
    else do
        (_, _, look, _) <- get
        case (M.lookup name look) of
            (Just (t, _, _)) -> return $ Just t
            otherwise -> return Nothing

updateClasses :: Ident -> ClassEnv -> StateT Env IO ()
updateClasses className def = do
    (vars, decls, funs, class_) <- get
    put(vars, decls, funs, M.insert className def class_)
    return ()


getVars :: StateT Env IO (VEnv)
getVars = do
    (v, _, _, _) <- get
    return v

getDecls :: StateT Env IO (VEnv)
getDecls = do
    (_, d, _, _) <- get
    return d


getFuns :: StateT Env IO (FEnv)
getFuns = do
    (_, _, f, _) <- get
    return f

getClasses :: StateT Env IO (CEnv)
getClasses = do
    (_, _, _, class_) <- get
    return class_

getClassDef :: Ident -> StateT Env IO (ClassEnv)
getClassDef name = do
    class_ <- getClasses
    (Just (fields, mets, parent)) <- return $ M.lookup name class_
    return (fields, mets, parent)

getClassFields :: Ident -> StateT Env IO (ClassField)
getClassFields name = do
    class_ <- getClasses
    (Just (fields, _, _)) <- return $ M.lookup name class_
    return fields

getClassMets:: Ident -> StateT Env IO (ClassMethod)
getClassMets name = do
    class_ <- getClasses
    (Just (_, mets, _)) <- return $ M.lookup name class_
    return mets

getClassParent :: Ident -> StateT Env IO (Maybe Ident)
getClassParent name = do
    class_ <- getClasses
    (Just (_, _, parent)) <- return $ M.lookup name class_
    return parent

existsMethod :: Ident -> Ident -> [(Type Debug, Ident)] -> StateT Env IO (Bool)
existsMethod name fun args = do
    mets <- (getClassMets name)
    args_ <- return $ map (\(t,(Ident n)) -> (getType t, Ident "")) args
    case (M.lookup fun mets) of
        Nothing -> return False
        (Just (_, params, _)) -> do
            mets_ <- return  $ map (\(t,n) -> (getType t, Ident "")) params
            return $ args_ == mets_


updateClassFields :: Ident -> (ClassField) -> StateT Env IO ()
updateClassFields name newFields = do
    (vars, decls, funs, class_) <- get
    (Just (fields, mets, parent)) <- return $ M.lookup name class_
    put(vars, decls, funs, M.insert name (newFields, mets, parent) class_)
    return ()

updateClassMets :: Ident -> ClassMethod -> StateT Env IO ()
updateClassMets name newMets = do
    (vars, decls, funs, class_) <- get
    (Just (fields, mets, parent)) <- return $ M.lookup name class_
    put(vars, decls, funs, M.insert name (fields, newMets, parent) class_)
    return ()

updateFuns :: Ident -> FunDef -> StateT Env IO ()
updateFuns funName def = do
    (vars, decls, funs, class_) <- get
    put(vars, decls, M.insert funName def funs, class_)
    return ()
