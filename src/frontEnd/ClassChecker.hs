{-
In currect version classes aren't implemented
but frontend has been made for further extensions.
-}

module ClassChecker where

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

import Data.Tuple

import Environment
import FrontEndErrors
import TypesStuff
import StmtChecker
import FunctionChecker
import Misc

newClass :: TopDefD -> StateT Env IO ()
newClass (ClassDef info classheader classblock) = do
    exists <- checkClassName classheader
    name <- return $ extractClassName classheader
    parent <- return $ extractParent classheader
    case exists of
        (Just i) -> classNameDupErr info i
        otherwise -> do
            updateClasses name (M.empty, M.empty, parent)
            (ClBlock a members) <- return classblock
            (fields, methods) <- return $ partition ifField members
            mapM (addField name) fields
            checkMethodsNames name methods
            mapM (addMethod name) methods
            return ()

checkMethodsNames :: Ident -> [ClassStmt Debug] -> StateT Env IO ()
checkMethodsNames name methods = do
    funNames <- mapM hashMethod (reverse methods)
    funInfos <- mapM methodInfo (reverse methods)
    dups <- return $ repeated funNames
    if((length dups) > 0) then do
        dup <- return $ fromJust $ elemIndex (head dups) funNames
        dup_name <- return $ fst (funInfos !! dup)
        dup_pos <- return $ getTypeInfo (snd $ funInfos !! dup)
        liftIO $ putStrLn $ (show dup_pos) ++ ": Redefinition of function " ++ (show dup_name)
        liftIO $ exitFailure
    else return ()

addMethod :: Ident -> ClassStmt Debug -> StateT Env IO ()
addMethod name (ClFun a type_ ident@(Ident funName) args block) = do
    (fields, mets, parent) <- getClassDef name
    params <- return $ map addMethodHelper args
    args_names <- return $ map (\(t, n) -> (n)) params
    case (findDupArgs args_names) of
        Nothing -> do
            updated <- return $ M.insert ident (type_, params, block) mets
            updateClassMets name updated
            return ()
        (Just (Ident var)) -> do
            liftIO $ putStrLn $ (show $ fromJust a) ++ ": Duplicated name of argument " ++ (var)
            liftIO $ exitFailure
            return ()

---------------------------------------------
-------------------
---------------------------------------------
addField :: Ident -> ClassStmt (Maybe (Int, Int)) -> StateT Env IO ()
addField name (ClVar a type_ items) = do
    mapM (addFieldHelper name type_) items
    return ()

addFieldHelper :: Ident -> TypeD -> Item (Maybe (Int, Int))-> StateT Env IO ()
addFieldHelper name type_ (NoInit info ident) = do
    fields <- getClassFields name
    case (M.lookup ident fields) of
        (Just i) -> classFieldDupErr info i ident
        otherwise -> do
            updated <- return $ M.insert ident type_ fields
            updateClassFields name updated
------------------------------------------


classChecker :: StateT Env IO ()
classChecker = do
    class_ <- getClasses
    names <- return $ M.toList class_
    (extends, roots) <- return $ partition (\(cl, (_, _, x)) -> isJust x) names
    (root_names, _) <- return $ unzip roots
    (classes_names, _) <- return $ unzip names
    empties <- return $ replicate (length classes_names) ([]::[Ident])
    mapped <- return $ M.fromList $ zip classes_names empties
    parents <-  mapM getClassParent classes_names
    vertices <- return $ zip parents classes_names
    (children, _) <- return $ partition (\(x, _) -> isJust x) vertices
    tree <- return $ map (\(x,a) -> (fromJust x, a)) children
    graph <- accMap tree mapped
    visited <- return $ zip classes_names (replicate (length classes_names) 0)
    mapM (checkIfCycle (Nothing) True  (M.fromList visited) graph) (classes_names)
    mapM (checkClass (Nothing) graph) root_names
    return ()

accMap :: [(Ident, Ident)] -> M.Map (Ident) [Ident] -> StateT Env IO (M.Map Ident [Ident])
accMap [] m = return m
accMap ((parent, child):xs) map_ = do
        case (M.lookup parent map_) of
            (Just x) ->
                accMap xs (M.insert parent (child:x) map_)
            Nothing -> do
                liftIO $ putStrLn "ERROR"
                liftIO $ exitFailure


checkClass :: Maybe Ident -> M.Map Ident [Ident] -> Ident -> StateT Env IO ()
checkClass parent tree node = do
    liftIO $ putStrLn $ show node
    if(isJust parent) then do
        perfomInheritance (fromJust parent) node
    else return ()
    children <- return $ fromJust $ M.lookup node tree
    mapM (checkClass (Just node) tree) children
    return ()

checkIfCycle :: Maybe Ident -> Bool -> M.Map Ident Int -> M.Map Ident [Ident] -> Ident -> StateT Env IO  ()
checkIfCycle parent fromQ visited tree node = do
    liftIO $ putStrLn $ show node
    if(fromQ == True && (M.lookup node visited) == Just 1)  then return ()
    else do
        if((M.lookup node visited) == Just 1) then do
            liftIO $ putStrLn $ show "CYCLE ERROR " ++ (show node) ++ ", " ++ (show parent)
            liftIO $ exitFailure
        else do
            updated <- return $ M.insert node 1 visited
            children <- return $ fromJust $ M.lookup node tree
            mapM (checkIfCycle (Just node) False updated tree) children
            return ()

--type ClassField =  M.Map Ident TypeD
--type ClassMethod =  M.Map Ident FunDef
--type ClassEnv = (ClassField, ClassMethod, Maybe Ident)
--(TypeD, [(TypeD, Ident)], BlockD)
perfomInheritance :: Ident -> Ident ->  StateT Env IO ()
perfomInheritance parent node = do
    class_ <- getClasses
    name <- return $ node
    (pFields, pMeths, _)<- getClassDef parent
    (cFields, cMeths, p)<- getClassDef node
    newFields <- return $ M.union cFields pFields
    newMeths <- traverseMets (M.toList pMeths) cMeths
    updateClasses node (newFields, newMeths, p)
    return ()

traverseMets ::[(Ident, FunDef)] -> ClassMethod -> StateT Env IO (ClassMethod)
traverseMets [] mets = return mets
traverseMets (x:xs) mets = do
    ret <-(checkParentDup x mets)
    traverseMets xs ret


checkParentDup :: (Ident, FunDef) -> ClassMethod -> StateT Env IO (ClassMethod)
checkParentDup (name, fun@(ret, args, Block a stmts)) mets = do
    def <- return $ M.lookup name mets
    case def of
        (Just (r,b,Block c _)) -> do
            parent_def <- return $ (getType ret, map (\(t, n) -> (getType t, Ident "")) args, Block a [])
            child_def <- return $ (getType r, map (\(t, n) -> (getType t, Ident "")) b, Block c [])
            if(parent_def == child_def) then return $ M.insert name fun mets
            else do
                liftIO $ putStrLn $ "ERROR"
                liftIO $ exitFailure
        otherwise -> do
            return $ M.insert name fun mets

------------------------------------------------------------
--addField ClFun a type_ ident args block =
checkClassName  :: ClassHeader a -> StateT Env IO (Maybe TypeD)
checkClassName (ClassDec a name) = checkName True name
checkClassName  (ClassDecExt a name parent) =  checkName True name

extractParent :: ClassHeader a -> Maybe Ident
extractParent (ClassDec a name) = Nothing
extractParent (ClassDecExt a name parent) =  Just parent

ifField :: ClassStmt a -> Bool
ifField (ClVar _ _ _) = True;
ifField (ClFun _ _ _ _ _) = False;

hashParams :: (TypeD, Ident) -> String
hashParams (t, i) = hashType t

extractClassName :: ClassHeader a -> Ident
extractClassName (ClassDec a ident) = ident
extractClassName  (ClassDecExt a ident1 ident2) = ident1

hashMethod :: ClassStmt (Maybe (Int, Int)) -> StateT Env IO (Ident, [(TypeD, Ident)])
hashMethod (ClFun a type_ ident@(Ident funName) args block) = do
    par <- return $ map addMethodHelper args
    return $ (ident, map (\(t, _) -> (getType t, Ident "")) par)


methodInfo :: ClassStmt (Maybe (Int, Int)) -> StateT Env IO (Ident, TypeD)
methodInfo (ClFun a type_ ident@(Ident funName) args block) =  do
    return (ident, type_)

addMethodHelper :: Arg (Maybe (Int, Int)) -> (TypeD, Ident)
addMethodHelper (Arg a type_ ident) = (type_, ident)


methodChecker :: StateT Env IO ()
methodChecker = do
    classes <- getClasses
    bodies <- return $ M.elems classes
    mapM execClass bodies
    return ()

--addFun :: Ident -> TypeD -> [(TypeD, Ident)] -> BlockD -> StateT Env IO ()

execClass :: ClassEnv -> StateT Env IO ()
execClass (fields, mets, _) = do
    backup <- get
    class_ <- getClasses
    put(M.empty, M.empty, M.empty, class_)
    fields_ <- return $ map swap (M.toList fields)
    fields' <- return $ map (\((t), i) -> (t, NoInit (Just $ getTypeInfo t) i)) fields_
    mapM (uncurry itemOperator) fields'
    funs <- return $ M.toList mets
    mapM execMethod funs
    (_, _, f, _) <- get
    liftIO $ putStrLn $ show f
    functionChecker
    return ()

execMethod :: (Ident, FunDef) -> StateT Env IO ()
execMethod (ident, (ret, args, body)) = do
    addFun ident ret args body
    liftIO $ putStrLn $ show ident
    return ()
