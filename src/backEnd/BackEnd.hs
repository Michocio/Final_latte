{-
Module that generate final llvm code.
It operates on intermediate code from middle level of project
and writes to file final code.
-}
module BackEnd where


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
import System.Environment
import System.FilePath


import Environment
import TypesStuff
import Misc
import IntermediateEnv


type Code = [String]
type VarsTypes = M.Map Argument (Type (Maybe (Int, Int)))
type FunsTypes = M.Map Ident (Type (Maybe (Int, Int)))
type StringEnv = M.Map String Int
type EnvBack = (Code, VarsTypes, FunsTypes, StringEnv)

targetData = "target datalayout = \"e-m:e-i64:64-f80:128-n8:16:32:64-S128\"\n"
targetDef = "target triple = \"x86_64-unknown-linux-gnu\"\n"

initialEnvBack = ([targetData, targetDef], M.empty,
     M.fromList [(Ident "printString", Void Nothing ),
    (Ident "printInt", Void Nothing ),
    (Ident "readInt", Int Nothing ),
    (Ident "readString", Str Nothing ),
    (Ident "error", Void Nothing ),
    (Ident "concat", Str Nothing )  ],
      M.empty)

printIntDecl = "declare void @printInt(i32)"
printStrDecl = "declare void @printString(i8*)"
readIntDecl = "declare i32 @readInt()"
readStrDecl = "declare i8* @readString()"
concatDecl = "declare i8* @concat(i8*, i8*)"
errorDecl = "declare void @error()\n\n"

fundDelsCode = [printIntDecl, printStrDecl, readIntDecl, readStrDecl, concatDecl, errorDecl]

writeToCode :: String ->  StateT EnvBack IO ()
writeToCode instr = do
    (code, vars, funs, strs) <- get
    put(code ++ [instr ++ "\n"], vars, funs, strs)

generateLLVM :: String -> [FunctionDef]  -> IO ()
generateLLVM file p =  (liftIO $ evalStateT (backEnd file p) initialEnvBack)

backEnd :: String -> [FunctionDef] -> StateT EnvBack IO ()
backEnd file graph = do
    mapM writeToCode fundDelsCode
    mapM traverseFuns graph
    new_graph <- mapM changeCode graph
    (code, vars, funs, strs) <- get
    strings <- return $ map swap (M.toList strs)

    mapping <- return $ map (\(nr, str) -> ("@.str." ++ (show nr) ++
         " = private constant [" ++ (show $ (length str) + 1) ++ " x i8] c\"" ++ ( str) ++ "\\00\"" )) strings
    mapM writeToCode mapping

    mapM (emitFunction) new_graph

    (code, _, _, _) <- get
    liftIO $ writeFile ((dropExtension file) ++ ".ll") (foldr (++) "" code)
    return ()

extractStrings :: Tuple -> StateT EnvBack IO ()
extractStrings (TEXT, s, _, _) =  do
    ifString s
    return ()
extractStrings (op, arg1, arg2, arg3) =  do
    ifString arg1
    ifString arg2
    ifString arg3
    return ()

ifString :: Argument -> StateT EnvBack IO ()
ifString (ValStr str) = do
    (code, vars, funs, strs) <- get
    if(isJust $ M.lookup str strs) then return ()
    else do
        num <- return $ M.size strs
        put(code, vars, funs, M.insert (str) num strs)
        (code, vars, funs, strs) <- get
        return ()
ifString _ = return ()

changeCode :: FunctionDef -> StateT EnvBack IO (FunctionDef)
changeCode (ident@(Ident name), type_, params, order, code_) = do
    (code, vars, funs, strs) <- get
    put(code, M.empty, funs, strs)
    codes <- return $ map fst (map snd (M.toList code_))
    mapM traverseAllocs codes
    mapM traverseAllocs codes
    new_blocks <- mapM (upgradeCode code_ type_) $ zip [0..M.size code_] (map snd (M.toList code_))
    new_code <- return $ M.fromList (zip (map fst (M.toList code_)) new_blocks)
    return (ident, type_, params, order, new_code)

removePhis :: M.Map Int Vertex -> Int  -> ([Tuple],[Tuple]) -> StateT EnvBack IO ([Tuple])
removePhis graph _ ([], new_code) = return new_code
removePhis graph me (((Phi, res, SSA phis, NIL):xs), new_code) = do
    bs <- return $ map (\(From b x) -> b) phis
    ans <- mapM (checkIfJump me graph) bs
    new_phis <- return $ removeIndecies ans 0 (phis, [])
    removePhis graph me ((xs), new_code ++ [(Phi, res, SSA new_phis, NIL)])
removePhis graph me ((x:xs), new_code) =
    removePhis graph me ((xs), new_code ++ [x])

removeIndecies :: [Bool] -> Int -> ([a],[a]) -> [a]
removeIndecies to_del index ([], old) = old
removeIndecies to_del index ((x:xs), old) =
    if(((!!) to_del index )== False) then
        removeIndecies to_del (index +1) (xs, old)
    else
        removeIndecies to_del (index + 1) (xs, old ++ [x])

checkIfJump :: Int -> M.Map Int Vertex -> Int -> StateT EnvBack IO (Bool)
checkIfJump me graph node = do
    (code, n) <- return $ fromJust $ M.lookup node graph
    case (last code) of
        (Br, _, Label _ l1, Label _ l2) -> do
            if(l1 == me || l2 == me) then return True
            else return False
        (GotoOp, Label _ l, _, _) -> do
            if(l == me) then return True
            else return False
        otherwise -> return False


upgradeCode ::  M.Map Int Vertex ->  (Type (Maybe(Int, Int))) -> (Int, Vertex) -> StateT EnvBack IO (Vertex)
upgradeCode g t (me, (block, n)) = do
    ok <- changeBlock me g t block
    return $ (ok, n)

changeBlock ::  Int -> M.Map Int Vertex -> (Type (Maybe(Int, Int))) -> [Tuple] -> StateT EnvBack IO ([Tuple])
changeBlock  me g t code = do
    first_code <- removePhis g me (code, [])
    new_code <- changeCalls t (first_code, []) []
    fin_code <- changeCalls t (new_code, []) []
    mapM extractStrings fin_code
    final <- mapM (changeCast) fin_code
    removed <- return $ map (removeDummyTuple) final
    cleared <- return $ map ((fromJust)) (filter (isJust) removed)
    return cleared

changeCast :: Tuple -> StateT EnvBack IO Tuple
changeCast (BitCast, res, len, GlobalVar s) = do
    (code, vars, funs, str) <- get
    (Just x) <- return $ M.lookup (s) str
    return (BitCast, res, len, GlobalVar $ ".str." ++ (show x))
changeCast z = return z

traverseFuns :: FunctionDef -> StateT EnvBack IO ()
traverseFuns (ident@(Ident name), type_, params, order, code_) = do
    (code, vars, funs, str) <- get
    codes <- return $ map fst (map snd (M.toList code_))
    put(code, vars, M.insert ident (rawType type_) funs, str)
    --mapM traverseAllocs codes
    return ()

staticType :: Argument -> StateT EnvBack IO (Type (Maybe(Int, Int)))
staticType v@(Reg nr) = do
    (code, vars, funs, str) <- get
    case (M.lookup v vars) of
        (Just x) -> return x
        otherwise -> return $ Int Nothing
staticType v@(Var name nr _ _) = do
    (code, vars, funs, str) <- get
    case (M.lookup v vars) of
        (Just x) -> return x
        otherwise -> return $ Int Nothing
staticType (ValInt _) = return $ Int Nothing
staticType (ValBool _) = return $ Bool Nothing
staticType (ValStr _) = return $ Str Nothing

changeCalls :: (Type (Maybe(Int, Int))) -> ([Tuple], [Tuple]) -> [(Type (Maybe(Int, Int)), Argument)] -> StateT EnvBack IO ([Tuple])
changeCalls t ([], new_code) _ = return new_code
changeCalls t ((instr@(AddOp, res, arg1, arg2):xs),new_code) params = do
    (code, vars, funs, str) <- get
    if(ifVar res) then do
        found <- lookForVar res
        if(not $ isJust $ found) then
            changeCalls t (xs, new_code ++ [instr]) []
        else do
            found <- lookForVar res
            (Just type_) <- return $ found
            --put(code, M.insert res type_ vars, funs, str)
            if(type_ == (Str Nothing)) then do
                new_instr <- return $ (CONCAT, res, arg1, arg2)
                changeCalls t (xs, new_code ++ [new_instr]) []
            else do
                new_instr <- return $ (AddOp, res, arg1, arg2)
                changeCalls t (xs, new_code ++ [new_instr]) []
    else do
        case (res) of
            (Reg nr) -> do
                if(not $ isJust $ M.lookup res vars ) then
                    changeCalls t (xs, new_code ++ [instr]) []
                else do
                    (Just type_) <- return $ M.lookup res vars
                    --put(code, M.insert res type_ vars, funs, str)
                    if(type_ == (Str Nothing)) then do
                        new_instr <- return $ (CONCAT, res, arg1, arg2)
                        changeCalls t (xs, new_code ++ [new_instr]) []
                    else do
                        new_instr <- return $ (AddOp, res, arg1, arg2)
                        changeCalls t (xs, new_code ++ [new_instr]) []
            otherwise -> do
                (type_) <- return $ typeLLVM res
                put(code, M.insert res (rawType type_) vars, funs, str)
                if(type_ == (Str Nothing)) then do
                    new_instr <- return $ (CONCAT, res, arg1, arg2)
                    changeCalls t (xs, new_code ++ [new_instr]) []
                else do
                    new_instr <- return $ (AddOp, res, arg1, arg2)
                    changeCalls t (xs, new_code ++ [new_instr]) []
changeCalls t (((ParamOp, arg, NIL, NIL):xs),new_code) params = do
    res <- staticType arg
    changeCalls t (xs, new_code) (params ++ [(res, arg)])
changeCalls t ((instr@(CallOp, (Fun name), res, NIL):xs),new_code) params = do
    (code, vars, funs, str) <- get
    (Just type_) <- return $ M.lookup (Ident name) funs
    new_instr <- return $ (CallFun type_, res, Fun name, Args params)
    put(code, M.insert res (rawType type_) vars, funs, str)
    changeCalls t (xs, new_code ++ [new_instr]) []
changeCalls t ((instr@(Icmp how, res, arg1, arg2):xs),new_code) params = do
    (code, vars, funs, str) <- get
    if(ifVar arg1) then do
        found <- lookForVar arg1
        if(not $ isJust $ found) then
            changeCalls t (xs, new_code ++ [instr]) []
        else do
            found <- lookForVar arg1
            (Just type_) <- return $ found
            new_instr <- return $ (IcmpTyped type_ how, res, arg1, arg2)
            changeCalls t (xs, new_code ++ [new_instr]) []
    else do
        case (arg1) of
            (Reg nr) -> do
                if(not $ isJust $ M.lookup arg1 vars ) then
                    changeCalls t (xs, new_code ++ [instr]) []
                else do
                    (Just type_) <- return $ M.lookup arg1 vars
                    new_instr <- return $ (IcmpTyped type_ how, res, arg1, arg2)
                    changeCalls t (xs, new_code ++ [new_instr]) []
            otherwise -> do
                (type_) <- return $ typeLLVM arg1
                new_instr <- return $ (IcmpTyped type_ how, res, arg1, arg2)
                changeCalls t (xs, new_code ++ [new_instr]) []
changeCalls t ((instr@(Phi, res, SSA phis, NIL):xs), new_code) params = do
    (code, vars, funs, str) <- get
    if(ifVar res) then do
        found <- lookForVar res
        if(not $ isJust $ found) then
            changeCalls t (xs, new_code ++ [instr]) []
        else do
            found <- lookForVar res
            (Just type_) <- return $ found
            new_instr <- return $ (PhiTyped type_, res, SSA phis, NIL)
            changeCalls t (xs, new_code ++ [new_instr]) []
    else do
        found <- return $ M.lookup res vars
        if(not $ isJust $ found) then
            changeCalls t (xs, new_code ++ [instr]) []
        else do
            found <- return $ M.lookup res vars
            (Just type_) <- return $ found
            new_instr <- return $ (PhiTyped type_, res, SSA phis, NIL)
            changeCalls t (xs, new_code ++ [new_instr]) []
changeCalls t (((RetOp, a, NIL, NIL):xs), new_code) params =
    return $ new_code ++ [(RetOpTyped t, a, NIL, NIL)]
changeCalls t ((x:xs),new_code) params = do
    changeCalls t (xs, new_code ++ [x]) (params)

traverseAllocs :: [Tuple] -> StateT EnvBack IO ()
traverseAllocs [] = return ()
traverseAllocs ((Alloca t, (Var name nr _ _), NIL, NIL):xs) = do
    (code, vars, funs, str) <- get
    put(code, M.insert (Var name nr 0 0) (rawType t) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((op@AddOp, var, val, a2):xs) = do
    (code, vars, funs, str) <- get
    if(ifVar val) then do
        found <- lookForVar val
        if(not $ isJust $ found) then return ()
        else do
            (Just type_) <- return $ found
            put(code, M.insert var (rawType type_) vars, funs, str)
            return ()
    else do
        case (val) of
            (Reg nr) -> do
                if(not $ isJust $ M.lookup val vars) then return ()
                else do
                    (Just type_) <- return $ M.lookup val vars
                    put(code, M.insert var (rawType type_) vars, funs, str)
            otherwise -> do
                (type_) <- return $ typeLLVM val
                put(code, M.insert var (rawType type_) vars, funs, str)
        return ()
    --put(code, M.insert res (Int Nothing) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((op@SubOp, res, a1, a2):xs) = do
    (code, vars, funs, str) <- get
    put(code, M.insert res (Int Nothing) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((op@MulOp, res, a1, a2):xs) = do
    (code, vars, funs, str) <- get
    put(code, M.insert res (Int Nothing) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((op@ModOp, res, a1, a2):xs) = do
    (code, vars, funs, str) <- get
    put(code, M.insert res (Int Nothing) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((op@NotOp, res, a1, a2):xs) = do
    (code, vars, funs, str) <- get
    put(code, M.insert res (Bool Nothing) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((op@NegOp, res, a1, a2):xs) = do
    (code, vars, funs, str) <- get
    put(code, M.insert res (Int Nothing) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((op@DivOp, res, a1, a2):xs) = do
    (code, vars, funs, str) <- get
    put(code, M.insert res (Int Nothing) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((BitCast, res, len, GlobalVar s):xs) = do
    (code, vars, funs, str) <- get
    put(code, M.insert res (Str Nothing) vars, funs, str)
    traverseAllocs xs
traverseAllocs (instr@(CallOp, (Fun name), res, NIL):xs) = do
    (code, vars, funs, str) <- get
    (Just type_) <- return $ M.lookup (Ident name) funs
    put(code, M.insert res (rawType type_) vars, funs, str)
    traverseAllocs xs
traverseAllocs ((Phi, var, SSA a, b):xs) = do
    (code, vars, funs, str) <- get
    (From _ val) <- return $ head a
    if(ifVar val) then do
        found <- lookForVar val
        if(not $ isJust $ found) then return ()
        else do
            (Just type_) <- return $ found
            put(code, M.insert var (rawType type_) vars, funs, str)
            return ()
    else do
        case (val) of
            (Reg nr) -> do
                if(not $ isJust $ M.lookup val vars) then return ()
                else do
                    (Just type_) <- return $ M.lookup val vars
                    put(code, M.insert var (rawType type_) vars, funs, str)
            otherwise -> do
                (type_) <- return $ typeLLVM val
                put(code, M.insert var (rawType type_) vars, funs, str)
        return ()
    traverseAllocs xs
traverseAllocs (x:xs) = traverseAllocs xs


lookForVar :: Argument ->  StateT EnvBack IO (Maybe (Type (Maybe(Int, Int))))
lookForVar (Var name nr _ _) = do
    (code, vars, funs, str) <- get
    return $ M.lookup (Var name nr 0 0) vars

emitFunction :: FunctionDef -> StateT EnvBack IO ()
emitFunction ((Ident name), type_, params, order, code) = do
    writeToCode $ "define "
        ++ (typeSize type_) ++ " @" ++ name ++ "(" ++  (intercalate ", " $ map llvmArg params) ++")"
    writeToCode "{"
    llvmCode order code
    writeToCode "}"

llvmCode :: [Int] -> M.Map Int Vertex -> StateT EnvBack IO ()
llvmCode [] graph = return ()
llvmCode (nr:xs) graph = do
    (Just (block, _)) <- return $ M.lookup nr graph
    if(length block == 0) then return ()
    else do
        writeToCode $ "l" ++ (show nr) ++ ":"
        mapM (writeToCode . printTuple) block
        llvmCode xs graph

llvmArg :: (Type (Maybe (Int, Int)), Ident) -> String
llvmArg (t, (Ident name)) = (typeSize t) ++ " %" ++ name ++ "_0_0_0"
