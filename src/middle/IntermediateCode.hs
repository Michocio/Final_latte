{-
Generates intermediate code from abstract syntex tree
-}

module IntermediateCode where


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
import Data.Function (on)


import Environment
import TypesStuff
import IntermediateEnv
import Misc
import Optimisations
import BackEnd

type SimpleBlocks = M.Map Argument [Tuple]
type ControlFlow = (Argument, [Argument])


generateIntermediate :: ProgramD -> IO ([FunctionDef])
generateIntermediate p =  (liftIO $ evalStateT (genProgram p) initialEnvMid)


genProgram :: ProgramD -> StateT EnvMid IO ([FunctionDef])
genProgram (Program info []) = return []
genProgram  (Program info (x:xs)) = genTopDef [] (x:xs)

genTopDef :: ([FunctionDef]) -> [TopDefD] -> StateT EnvMid  IO ([FunctionDef])
genTopDef code [] = return code
genTopDef code (x:xs) = do
    fun <- genTopInstr x
    genTopDef (code++[fun]) xs

genBlocks :: [(Argument, (Int, Int))] -> [Tuple] -> SimpleBlocks -> SimpleBlocks
genBlocks [] _ graph = graph
genBlocks ((arg, (start, end)):xs) code graph =
    genBlocks xs (drop (end - start + 1) code) (M.insert arg (take (end - start + 1) code) graph)

returnJump :: Int -> [Int] -> [Tuple] -> [Int]
returnJump _ old [] = old
--returnJump x old (((IfOp how), a1, a2, (Label _ pos)):xs) = returnJump (x+1) (x:old) xs
--returnJump x old ((GotoOp, (Label _ pos), _, _):xs) = returnJump (x+1) (x:old) xs
--returnJump x old ((RetOp, _, _, _):xs) = returnJump (x+1) (x:old) xs
returnJump y old (x:xs) = returnJump (y+1) old xs

genTopInstr :: TopDefD -> StateT EnvMid IO (FunctionDef)
genTopInstr fun@(FnDef a type_ ident@(Ident name) args block@(Block t code)) = do
    put initialEnvMid
    lEntry <- genLabel "entry"
    emit(START, NIL, NIL, NIL)
    params <- return $ map (\(Arg _ t n) ->(t,n)) args
    edited <- return $ addArguments (params) code
    if(length code == 0) then
        emit(RetOp, NIL, NIL, NIL)
    else return ()
    mapM genStmt edited
    (order, code) <- printCode
    return (ident, type_, params, order, code)

addArguments :: [(TypeD, Ident)] -> [Stmt (Maybe (Int, Int))] -> ([Stmt (Maybe (Int, Int))])
addArguments [] x = x
addArguments ((t,ident):xs) block =
    addArguments xs ((Decl Nothing t [(NoInit Nothing ident)]):block)

removeDeadCode :: [Tuple] -> [Tuple]
removeDeadCode code =
    case (findIndex dropAfterRet code) of
        (Nothing) -> code
        (Just i) -> take i code


reorderBlocks :: [Int] -> [((String, Int), Int)] -> [Int] -> [Int]
reorderBlocks final [] curr = curr
reorderBlocks final ((_, nr):orginal) curr =
    if(nr `elem` final) then reorderBlocks final orginal (curr ++ [nr])
    else reorderBlocks final orginal curr

printCode :: StateT EnvMid IO ([Int], M.Map Int Vertex)
printCode = do
    emit(EmptyOp, NIL, NIL, NIL)
    --putEntryLabel
    removeDupLabels
    sortedLabels <- showCode -- orginal code ordered

    (blocks, graph) <- createBlockGraph sortedLabels
    --blocks - already sorted

    labels_ordered <- return $ map fst (M.toList blocks)
    labels_orginal <- return $ reorderBlocks labels_ordered sortedLabels []
    nums <- return [0.. (length labels_ordered)]
    labels_mapped <- return $ M.fromList $ zip (sort labels_orginal) nums

    enumed <- mapM enumVars (M.toList blocks)

    neighbors <- return $ map snd (M.toList graph)
    codes <- return enumed
    booles <- return $ replicate (length codes) False
    maps <- return $ replicate (length codes) M.empty
    maps_ <- return $ replicate (length codes) M.empty
    node <- return $ zip5 neighbors codes booles maps maps_
    tree <- return $ M.fromList $ zip labels_ordered node
    (graph, _, _)<- return $ runIdentity $ execStateT (blockDfs 0 0) (tree, M.empty,M.empty)
    (_, codes, _, phis, _) <- return $ unzip5 $ map snd (M.toList graph)
    packed <-return $ zip3 labels_ordered (map M.toList phis) codes


    cor <- mapM createPhis packed

    showBlocks labels_orginal labels_mapped  cor
    edited <- doOpt cor
    (a,b) <- aliveVar ([],[]) (foldr (++) [] edited)
    k <- return $ map (map (removeDeadUsage b)) edited
    z <- return $ map ((filter isJust)) k
    zz <- return $ map (map fromJust) z

    conds <- mapM (replaceIf []) zz
    alwaysBr <- mapM (addJumps) (zip conds neighbors)

    final_code <- return $ M.fromList $ zip labels_ordered (zip alwaysBr neighbors)
    return (labels_orginal, final_code)

addJumps :: ([Tuple],[Argument]) -> StateT EnvMid IO [Tuple]
addJumps ([],neighbors) = do
    if(length neighbors == 0) then return []
    else do
        new_instr <- return (GotoOp, (head neighbors), NIL, NIL)
        return [new_instr]
addJumps (code, neighbors) = do
    case (last code) of
        (GotoOp, lab, NIL, NIL) -> return code
        (Br, t, l1, l2) -> do
            if(length neighbors == 0) then return code
            else do
                if((head neighbors) == l1) then do
                    new_instr <- return (Br, t, l1, (last neighbors))
                    return $ (init code) ++ [new_instr]
                else do
                    new_instr <- return (Br, t, l1, (head neighbors))
                    return $ (init code) ++ [new_instr]
        otherwise -> do
            if(length neighbors == 0) then return code
            else do
                new_instr <- return (GotoOp,(head neighbors), NIL, NIL)
                --return $ (init code) ++ [new_instr]
                return $ (code) ++ [new_instr]



newPhi :: Int -> ((String, Int), [Argument]) ->  StateT EnvMid IO Tuple
newPhi block ((name, nr), phi) = do
    if(length phi == 1) then do
        (From b x) <- return $ head phi
        return (AssOp, (Var name nr 0 block), x, NIL)
    else
        return (Phi, (Var name nr 0 block), SSA phi, NIL)

createPhis :: (Int, [((String, Int), [Argument])], [Tuple]) -> StateT EnvMid IO [Tuple]
createPhis (block, phis, code) = do
    new_code <- (mapM (newPhi block) phis)
    return $ (new_code )++ code


type EnumEnv = (M.Map (String,Int) Int)

enumVars :: (Int, [Tuple]) ->  StateT EnvMid IO ([Tuple])
enumVars (nr, code) = do
    x <-  return $ evalState (enumerator nr code) M.empty
    return x

enumerator :: Int -> [Tuple] -> State EnumEnv [Tuple]
enumerator nr code = do
    put (M.empty)
    mapM (nameVar nr) code

nameVar :: Int -> Tuple -> State EnumEnv  (Tuple)
nameVar nr (Alloca t, res, a1, a2) = do
    res_ <- replaceVar True nr res
    return (Alloca t, res_, NIL, NIL)
nameVar nr (IfOp op, a1, a2, x) = do
    arg1 <- countVars nr a1
    arg2 <- countVars nr a2
    return (IfOp op, arg1, arg2, x)
nameVar nr (RetOp ,res, NIL, NIL) = do
    res_ <- countVars nr res
    return (RetOp ,res_, NIL, NIL)
nameVar nr (ParamOp ,res, NIL, NIL) = do
    res_ <- countVars nr res
    return (ParamOp ,res_, NIL, NIL)
--nameVar nr (CallFun, res, name ,Args params) = do
--    res_ <- countVars nr res
--    args <- mapM (countVars nr) params
--    return (CallFun, res_, name ,Args args)
nameVar nr (op, res, a1, a2) = do
    arg1 <- countVars nr a1
    arg2 <- countVars nr a2
    res_ <- replaceVar False nr res
    return (op, res_, arg1, arg2)

replaceVar :: Bool-> Int -> Argument -> State EnumEnv (Argument)
replaceVar alloca id_ arg = do
    s <- get
    case (arg) of
        (Var name nr i _) -> do
            exists <- return $ M.lookup (name,nr) s
            case exists of
                (Just x) -> do
                    put(M.insert (name, nr) (x+1) s)
                    return $ (Var name nr (x+1) id_)
                otherwise -> do
                    if(alloca) then do
                        put(M.insert (name, nr) 0 s)
                        return $ (Var name nr  0 id_)
                    else do
                        put(M.insert (name, nr) 1 s)
                        return $ (Var name nr  1 id_)
        otherwise -> return arg

countVars ::  Int -> Argument -> State EnumEnv  (Argument)
countVars id_ arg = do
    s <- get
    case (arg) of
        (Var name nr i _) -> do
            exists <- return $ M.lookup (name,nr) s
            case exists of
                (Just x) -> do
                    return $ (Var name nr x id_)
                otherwise -> do
                    put(M.insert (name, nr) 0 s)
                    return $ (Var name nr 0 id_)
        otherwise -> return arg


blockDfs :: Int -> Int -> State FinEnv ()
blockDfs from node = do
    (graph, vars_start ,delcs) <- get
    put(graph, vars_start, M.empty)
    (graph, vars,delcs) <- get
    (Just (neighbors, code, visited, phis, allocs))<- return $ M.lookup node graph
    already <- return visited
    mapM (analyzeTuple from node) code

    (graph, vars,decls) <- get
    v_ <- return $ map fst (M.toList vars)
    d_ <- return $ map fst (M.toList decls)
    to_declare <- return $ (\\) v_ d_
    mapM (extendPhis from node) to_declare
    (graph, vars,decls) <- get

    if(already) then do
        put(graph, vars_start, M.empty)
        return ()
    else do
        nums <- return $ map (\(Label _ i) -> i) neighbors
        mapM (blockDfs node) nums
        (graph_, vars_,decls_) <- get
        put (graph_, vars_start, M.empty)
        return ()


extendPhis :: Int -> Int ->(String, Int) -> State FinEnv ()
extendPhis from node (name, nr) = do
    (graph, vars,decls) <- get
    (Just (neighbors, code, visited, phis, allocs))<- return $ M.lookup node graph
    (Just val) <- return $ M.lookup (name, nr) vars
    if(isJust $ M.lookup (name, nr) allocs) then return ()
    else do
        case (M.lookup (name, nr) phis) of
            Nothing -> do
                phi_new <- return $ M.insert (name, nr) [(From from val)] phis
                updated <- return (neighbors, code, True, phi_new, allocs)
                put(M.insert node updated graph, M.insert (name, nr) (Var name nr 0 node) vars, decls)
                return ()
            (Just x) -> do
                phi_new <- return $ M.insert (name, nr) ((From from val):x) phis
                updated <- return (neighbors, code, True, phi_new, allocs)
                put(M.insert node updated graph, M.insert (name, nr) (Var name nr 0 node) vars, decls)
                return ()


analyzeTuple :: Int -> Int -> Tuple -> State FinEnv ()
analyzeTuple from node (Alloca t, v@(Var name nr ord bl), a, b) = do
    (graph, vars, decls) <- get
    (Just (neighbors, code, visited, phis, allocs) )<- return $ M.lookup node graph
    updated <- return $ M.insert (name, nr) True allocs
    put(M.insert node (neighbors, code, True, phis, updated) graph, M.insert (name, nr) v vars, decls)
    return ()
analyzeTuple from node (AssOp, v@(Var name nr ord bl), arg1, a) = do
    analyzeArgument from node v
    analyzeArgument from node arg1
    (graph, vars, decls) <- get
    put(graph, M.insert (name, nr) v vars, decls)
    return ()
--analyzeTuple from node (IfOp how, arg1, arg2, res) = do
--    analyzeArgument from node arg1
--    analyzeArgument from node arg2
    --(graph, vars, decls) <- get
    --put(graph, M.insert (name, nr) v vars, decls)

analyzeTuple from node (op, v@(Var name nr ord bl), arg1, arg2) = do
    analyzeArgument from node arg1
    analyzeArgument from node arg2
    analyzeArgument from node v --ddsd
    (graph, vars, decls) <- get
    put(graph, M.insert (name, nr) v vars, decls)
    return ()
analyzeTuple from node (op, res, arg1, arg2) = do
    analyzeArgument from node arg1
    analyzeArgument from node arg2

-- sasiedzi, code, visited, wziete, u siebie aktualny stan
type FinEnv = (M.Map Int Node, M.Map (String, Int) Argument, M.Map (String, Int) Bool)
type Node = ([Argument], [Tuple], Bool, M.Map (String, Int) [Argument], M.Map (String, Int) Bool)
-- graf, visited, blocks,

analyzeArgument :: Int -> Int -> Argument -> State FinEnv ()
analyzeArgument from node (Var name nr ord bl) = do
    (graph, vars, decls) <- get
    (Just (neighbors, code, visited, phis, allocs)) <- return $ M.lookup node graph
    if(isJust $ M.lookup (name, nr) allocs) then return ()
    else
        case (M.lookup (name, nr) decls) of
            Nothing -> do
                decls_new <- return $ M.insert (name, nr) True decls
                case (M.lookup (name, nr) phis) of
                    Nothing -> do
                        (Just val) <-return $ M.lookup (name, nr) vars
                        phi_new <- return $ M.insert (name, nr) [(From from val)] phis
                        updated <-return (neighbors, code, True, phi_new, allocs)
                        put(M.insert node updated graph, vars, decls_new)
                        return ()
                    (Just x) -> do
                        (Just val) <-return $ M.lookup (name, nr) vars
                        phi_new <- return $ M.insert (name, nr) ((From from val):x) phis
                        updated <-return (neighbors, code, True, phi_new , allocs)
                        put(M.insert node updated graph, vars, decls_new)
                        return ()
            otherwise ->return ()
analyzeArgument from node x = return ()

createBlockGraph :: [((String, Int), Int)] -> StateT EnvMid IO (M.Map Int [Tuple], (M.Map Int [Argument]))
createBlockGraph sorted_blocks = do
    labels <- getLabels
    code <- getCode
    extractedBlocks <- return $ map (\(k,(l, pos)) -> (k, pos)) (M.toList labels)
    starts <- return $ sortBy (compare `on` (snd)) extractedBlocks
    (_,_,_,_, res) <- return $ genBlock (fst $ head starts, 0, code, tail starts, M.empty)
    ord <- return $ map fst $ map swap sorted_blocks
    sorted <- return $ sortMap ord res []
    acc <- genControlFlow sorted ord M.empty
    wynik <- traverseBlocks [] acc res M.empty (Label "l" (head ord))
    return (wynik, acc )

removeDupLabels :: StateT EnvMid IO ()
removeDupLabels = do
    labels <- getLabels
    code <- getCode
    same <- return $ map (\(nr, (_, code))-> (code, nr)) (M.toList labels)
    same_code_ <- return $ groupLabels same M.empty
    same_code <- return $ map snd (M.toList same_code_)
    mapM alterLabels same_code
    mapM eraseDupsLabels (map tail same_code)
    return ()

groupLabels :: [(Int, Int)] -> M.Map Int [Int] -> M.Map Int [Int]
groupLabels [] old = old
groupLabels ((c, nr):xs) old =
    case (M.lookup c old) of
        Nothing -> groupLabels xs (M.insert c [nr] old)
        (Just x) ->  groupLabels xs (M.insert c (x++[nr]) old)

eraseDupsLabels :: [Int] -> StateT EnvMid IO ()
eraseDupsLabels ls = do
    mapM deleteLabel ls
    return ()

alterLabels :: [Int] -> StateT EnvMid IO ()
alterLabels same = do
    if(length same == 1) then return ()
    else do
        leader <- return $ Label "l" (head same)
        changers <- return $ map (\x -> (Label "l" x)) (tail same)
        (vars, decls, temps, lab, code, labels, curr) <- get
        diff <- return $ map (changeLabel leader changers) code
        put(vars, decls, temps, lab, diff, labels, curr)
        return ()

changeLabel ::  Argument -> [Argument] -> Tuple -> Tuple
changeLabel  leader cands (IfOp a, b, c, y) = do
    if(y `elem` cands) then (IfOp a, b, c, leader)
    else (IfOp a, b, c, y)
changeLabel leader cands (GotoOp, y, a, b) = do
    if(y `elem` cands) then (GotoOp, leader, a, b)
    else (GotoOp, y, a, b)
changeLabel aleader cands a = a

traverseBlocks :: [Int] -> M.Map Int [Argument] -> M.Map Int [Tuple] -> M.Map Int [Tuple] ->
    Argument -> StateT EnvMid IO (M.Map Int [Tuple])
traverseBlocks visited graph orginal old (Label _ node) = do
    if(node `elem` visited) then return old
    else do
        me <- return $ fromJust $ M.lookup node orginal
        ch <- return $ fromJust $ M.lookup node graph
        children <-  mapM (traverseBlocks (node:visited) graph orginal (M.insert node me old)) ch
        return $ foldr (M.union) (M.insert node me old) children

sortMap :: [Int] -> M.Map Int [Tuple] -> [(Int, [Tuple])] ->  [(Int, [Tuple])]
sortMap [] map_ list_ =  list_
sortMap (x:xs) map_ list_ =
    if (isJust $ M.lookup x map_) then sortMap xs map_ (list_ ++ ([(x,fromJust $ M.lookup x map_)]))
    else sortMap xs map_ list_

genControlFlow :: [(Int, [Tuple])] -> [Int] -> M.Map Int [Argument] -> StateT EnvMid IO (M.Map Int [Argument])
genControlFlow [] _ x = return x
genControlFlow  ((nr, []):xs) (y:ys) graph = do
    if(length xs == 0) then return graph
    else genControlFlow xs ys (M.insert nr [Label "l" (head ys)] graph)
genControlFlow ((nr, code):xs) (y:ys) graph = do
    instr <- return $ last code
    case (instr) of
        (IfOp a, _, _, jmp) -> do
            if(length xs == 0) then
                genControlFlow xs  ys (M.insert nr [jmp] graph)
            else
                genControlFlow xs ys(M.insert nr ([Label "l" (head ys)]++ [jmp]) graph)
        (RetOp, _, _, _) -> do
            updated <- return $ M.insert nr [] graph
            genControlFlow xs  ys updated
        (GotoOp, jmp, _, _) -> do
            updated <- return $ M.insert nr [jmp] graph
            genControlFlow xs (ys) updated
        (otherwise) -> do
            if(length xs == 0) then
                genControlFlow xs ys (M.insert nr [] graph)
            else
                genControlFlow xs ys (M.insert nr ([Label "l" (head ys)]) graph)



dropAfterRet :: Tuple -> Bool
dropAfterRet (RetOp, _, _, _) = True
dropAfterRet _ = False

--index code labels old_map new labels new_map new index
genBlock :: (Int, Int, [Tuple], [(Int, Int)], M.Map Int [Tuple]) ->
    (Int, Int, [Tuple], [(Int, Int)], M.Map Int [Tuple])
genBlock (curr, index, [], [], blocks) = (curr, index, [], [], blocks)
genBlock (curr, index, code, [], blocks) = do
    case (M.lookup curr blocks) of
        Nothing -> (curr, index , [], [], M.insert curr code blocks)
        (Just x) -> (curr, index, [],[], M.insert curr (x++code) blocks)
genBlock (curr, index, [], labels, blocks) = (curr, index, [], labels, blocks)
genBlock (curr, index, (c:cx), ((nr, l):lx), blocks) = do
    if(index == l) then genBlock (nr, index, (c:cx), lx, blocks)
    else
        case (M.lookup curr blocks) of
            Nothing -> genBlock(curr, index + 1, cx, ((nr, l):lx), M.insert curr [c] blocks)
            (Just x) -> genBlock(curr, index + 1, cx, ((nr, l):lx), M.insert curr (x++[c]) blocks)


genItem :: Type (Maybe (Int, Int)) -> Item (Maybe (Int, Int)) -> StateT EnvMid IO ()
genItem  t (Init info (Ident name) expr) = do
    --emit(Alloca t, var, NIL, NIL)
    res <- genExpr expr
    var <- newVar name
    emit(Alloca t, var, NIL, NIL)
    emit(AssOp, var, res, NIL)
genItem t (NoInit info (Ident name)) =  do
    var <- newVar name
    emit(Alloca t, var, NIL, NIL)
    if(info /= Nothing) then do
        res <- genExpr (defaultValue t)
        emit(AssOp, var, res, NIL)
        return ()
    else return ()
    return ()

defaultValue :: Type (Maybe (Int, Int)) -> Expr (Maybe (Int, Int))
defaultValue (Int x) = ELitInt x 0
defaultValue (Str a) = EString a ""
defaultValue (Bool a) = ELitFalse a
defaultValue (Array a type_) = ELitFalse a

genStmt ::Stmt (Maybe(Int, Int)) -> StateT EnvMid IO ()
genStmt (Decl _ type_ items_) = do
    x <- mapM (genItem type_) items_
    return ()
genStmt  to@(BStmt jak (Block a stmts)) = do
    if(jak /= Nothing) then do
        lBlock <- genLabel "l"
        return ()
    else return ()
    (vars, decls, temps, labs, code, labels, curr) <- get
    --put(vars, decls, temps, labs, code, labels, curr)
    mapM genStmt stmts
    (vars_, _, temps_, labs_, code_, labels_, _) <- get
    put(vars_, decls, temps_, labs_, code_, labels_, curr)
    if(jak /= Nothing) then do
        lEnd <- genLabel "l"
        return ()
    else return ()
    return ()
genStmt  (SExp a expr) = do
    genExpr expr
    return ()
genStmt  (Ret info expr) = do
    ret <- genExpr expr
    emit(RetOp, ret, NIL, NIL)
genStmt  (VRet info) = emit(RetOp, NIL, NIL, NIL)
genStmt (Ass x lvalue@(ValArr a (Ident name) e) expr) = do
    val <- genExpr expr
    index <- genExpr e
    t <- freshTemp
    --emit(GetElemPtr, Var name 0 0 0, index, t)
    emit(Store, val, t, NIL)
genStmt (Ass x var@(ValVar a name) expr) = do
    res <- genExpr expr
    ident <- assingVar $ snd $ stringLValue var
    emit(AssOp, ident, res, NIL)
    --emit(Store, res, Var (snd $ stringLValue var) 0 0, NIL)
genStmt (Incr a val) = do
    --temp <- freshTemp
    --emit(Load, Var (snd $ stringLValue val) 0, temp, NIL)
    --t <- freshTemp
    old <-  getVar (snd $ stringLValue val)
    var <-  assingVar (snd $ stringLValue val)
    emit(AddOp, var, old, ValInt 1)
    --emit(Store, t, Var (snd $ stringLValue val) 0, NIL)
genStmt (Decr a val) = do
    old <-  getVar (snd $ stringLValue val)
    var <-  assingVar (snd $ stringLValue val)
    emit(SubOp, var, old, ValInt 1)
    --temp <- freshTemp
    --emit(Load, Var (snd $ stringLValue val) 0, temp, NIL)
    --t <- freshTemp
    --emit(SubOp, temp, ValInt 1, t)
    --emit(Store, t, Var (snd $ stringLValue val) 0, NIL)
genStmt  (Empty a) = return ()
genStmt  (Cond info cond ifBlock) = do
    case (cond) of
        (ELitTrue a) -> do
            lTrue_ <- genLabel "l"
            case (ifBlock) of
                (BStmt _ (Block _ code)) -> genStmt (BStmt Nothing $ Block Nothing code)
                otherwise ->  genStmt (BStmt Nothing $ Block Nothing [ifBlock])
        (ELitFalse a) -> return ()
        otherwise -> do
            lTrue_ <- reserveLabel "l"
            lTrue <- return $ Label  "l" lTrue_
            lEnd_ <- reserveLabel "l"
            lEnd <- return $ Label  "l" lEnd_
            genCond cond lTrue lEnd lTrue
            updateLabel lTrue_
            case (ifBlock) of
                (BStmt _ (Block _ code)) -> genStmt (BStmt Nothing $ Block Nothing code)
                otherwise ->  genStmt (BStmt Nothing $ Block Nothing [ifBlock])
            --emit(GotoOp, lEnd, NIL, NIL)
            updateLabel lEnd_
genStmt (CondElse info cond ifBlock elseBlock) = do
    case (cond) of
        (ELitTrue a) -> do
            lTrue_ <- genLabel "l"
            case (ifBlock) of
                (BStmt _ (Block _ code)) -> genStmt (BStmt Nothing $ Block Nothing code)
                otherwise ->  genStmt (BStmt Nothing $ Block Nothing [ifBlock])
        (ELitFalse a) -> do
            lFalse_ <-  genLabel "l"
            case (elseBlock) of
                (BStmt _ (Block _ code)) -> genStmt (BStmt Nothing $ Block Nothing code)
                otherwise ->  genStmt (BStmt Nothing $ Block Nothing [elseBlock])
        otherwise -> do
            lTrue_ <- reserveLabel "l"
            lTrue <- return $ Label  "l" lTrue_
            lFalse_ <- reserveLabel "l"
            lFalse <- return $ Label  "l" lFalse_
            lEnd_ <- reserveLabel "l"
            lEnd <- return $ Label  "l" lEnd_
            genCond cond lTrue lFalse lTrue
            updateLabel lTrue_
            case (ifBlock) of
                (BStmt _ (Block _ code)) -> genStmt (BStmt Nothing $ Block Nothing code)
                otherwise ->  genStmt (BStmt Nothing $ Block Nothing [ifBlock])
            emit(GotoOp, lEnd, NIL, NIL)
            updateLabel lFalse_
            case (elseBlock) of
                (BStmt _ (Block _ code)) -> genStmt (BStmt Nothing $ Block Nothing code)
                otherwise ->  genStmt (BStmt Nothing $ Block Nothing [elseBlock])
            updateLabel lEnd_
genStmt (While a expr stmt) = do
    case (expr) of
        (ELitTrue a) -> do
            lTrue_ <- genLabel "l"
            lEnd_ <- reserveLabel "l"
            lEnd <- return $ Label  "l" lEnd_
            genStmt (BStmt Nothing $ Block Nothing [stmt])
            emit(GotoOp, Label "l" lTrue_, NIL, NIL)
            updateLabel lEnd_
        (ELitFalse a) -> return ()
        otherwise -> do
            l1_ <- reserveLabel "l"
            l1 <- return $ Label  "l" l1_
            l2_ <- reserveLabel "l"
            l2 <- return $ Label  "l" l2_
            lEnd_ <- reserveLabel "l"
            lEnd <- return $ Label  "l" lEnd_
            emit(GotoOp, l2, NIL, NIL)
            updateLabel l1_
            genStmt (BStmt Nothing $ Block Nothing [stmt])
            updateLabel l2_
            genCond expr l1 lEnd lEnd
            updateLabel lEnd_

genCond :: Expr (Maybe (Int, Int)) -> Argument -> Argument -> Argument -> StateT EnvMid IO ()
genCond (ELitTrue a) lTrue lFalse lNext =
    emit(GotoOp, lTrue, NIL, NIL)
genCond (ELitFalse a) lTrue lFalse lNext = --do
    emit(GotoOp, lFalse, NIL, NIL)
genCond (EAnd _ e1 e2) lTrue lFalse lNext = do
    lMid_ <- (reserveLabel "l")
    lMid <- return $ Label  "l" lMid_
    genCond e1 lMid lFalse lMid
    updateLabel lMid_
    genCond e2 lTrue lFalse lNext
genCond (EOr _ e1 e2) lTrue lFalse lNext = do
    lMid_ <- (reserveLabel "l")
    lMid <- return $ Label  "l" lMid_
    genCond e1 lTrue lMid lMid
    updateLabel lMid_
    genCond e2 lTrue lFalse lTrue

genCond (Not _ e) lTrue lFalse lNext = genCond e lFalse lTrue lNext
genCond (ERel a expr1 relop_ expr2 ) lThen lElse lNext = do
    e1 <- genExpr expr1
    e2 <- genExpr expr2
    if(lNext == lThen) then do
        relop <- return $ compl relop_
        jmp <- return  lElse
        emitCond relop e1 e2 jmp
    else do
        if (lNext == lElse) then do
            relop <- return relop_
            jmp <- return  lThen
            emitCond relop e1 e2 jmp
        else do
            relop <- return  relop_
            jmp <- return  lThen
            emitCond relop e1 e2 jmp
            emit(GotoOp, lElse, NIL, NIL)
genCond e lThen lElse lNext = genCond (ERel Nothing e (EQU Nothing) (ELitTrue Nothing)) lThen lElse lNext

emitCond :: RelOp a-> Argument-> Argument-> Argument -> StateT EnvMid IO ()
emitCond relop e1 e2 jmp = do
    case (relop) of
        LTH x -> emit(IfOp LTHm, e1, e2, jmp)
        LE a -> emit(IfOp LEm, e1, e2,  jmp)
        GTH a -> emit(IfOp GTHm, e1, e2,  jmp)
        GE a -> emit(IfOp GEm, e1, e2, jmp)
        EQU a -> emit(IfOp EQUm, e1, e2, jmp)
        NE a -> emit(IfOp NEm, e1, e2, jmp)
    return ()

compl :: RelOp x -> RelOp x
compl (LTH a) = GE a
compl (LE a) = GTH a
compl (GTH a) =LE a
compl (GE a) = LTH a
compl (EQU a) =NE a
compl (NE a) = EQU a





genExpr :: Expr (Maybe(Int, Int))-> StateT EnvMid IO (Argument)
genExpr exp = case exp of
        EVar x lvalue@(ValVar a (Ident name)) -> do
            --temp <- freshTemp
            --emit(Load, Var (snd $ stringLValue lvalue) 0, temp, NIL)
            getVar name--temp
        EVar x lvalue@(ValArr a (Ident name) e) -> do
            index <- genExpr e
            t <- freshTemp
            emit(GetElemPtr (Var name 0 0 0) (Int Nothing), t, ValInt 10, index)
            res <- freshTemp
            emit(Load, t, res, NIL)
            return res
        --ENew a type_ -> do
        --    emit(New_Array type_, )
        ENewArr a type_ e -> do
            res <- freshTemp
            len <- genExpr e
            emit(New_Array type_, res, len, NIL)
            return res
        --ENullCast a type_ -> ENullCast (f a) (fmap f type_)
        EString a string -> do
            t <- freshTemp
            len <- return $ length string

            if(len > 0) then do
                emit(TEXT, ValStr (init $ tail string), NIL, NIL)
                emit(BitCast, t, ValInt ((toInteger len) - 1), GlobalVar $ (init $ tail string))
            else do
                emit(TEXT, ValStr "", NIL, NIL)
                emit(BitCast, t, ValInt (1), GlobalVar "")
            return t
        ELitInt a integer -> return $ ValInt integer
        ELitTrue a -> return $ ValBool True
        ELitFalse a -> return $ ValBool False
        Neg a expr -> do
            e <- genExpr expr
            t <- freshTemp
            emit (NegOp, t, e, ValInt (-1))
            return t
        Not a expr -> do
            e <- genExpr expr
            case (e) of
                (ValBool True) -> return $ ValBool False
                (ValBool False) -> return $ ValBool True
                otherwise -> do
                    t <- freshTemp
                    emit (NotOp, t, e, ValBool True)
                    return t
        EMul a expr1 mulop expr2 -> do
            e1 <- genExpr expr1
            e2 <- genExpr expr2
            t <- freshTemp
            case mulop of
                Times a -> emit(MulOp, t,e1, e2)
                Div a -> emit(DivOp, t,e1, e2)
                Mod a -> emit(ModOp, t,e1, e2)
            return t
        EAdd a expr1 addop expr2 -> do
            e1 <- genExpr expr1
            e2 <- genExpr expr2
            t <- freshTemp
            case addop of
                Plus a -> emit(AddOp, t,e1, e2)
                Minus a -> emit(SubOp, t, e1, e2)
            return t
        ERel a expr1 relop expr2 -> do
            e1 <- genExpr expr1
            e2 <- genExpr expr2
            lTrue <- reserveLabel "l"
            lFin <- reserveLabel "l"
            case (relop) of
                LTH x -> emit(IfOp LTHm, e1, e2, Label "l" lTrue)
                LE a -> emit(IfOp LEm, e1, e2,  Label "l" lTrue)
                GTH a -> emit(IfOp GTHm, e1, e2,  Label "l" lTrue)
                GE a -> emit(IfOp GEm, e1, e2, Label "l" lTrue)
                EQU a -> emit(IfOp EQUm, e1, e2,  Label "l" lTrue)
                NE a -> emit(IfOp NEm, e1, e2,  Label "l" lTrue)
            lFalse <- genLabel "l"
            t1 <- freshTemp
            emit(AssOp, t1, ValBool False, NIL)
            emit(GotoOp, Label "l" lFin, NIL, NIL)
            updateLabel lTrue
            t2 <- freshTemp
            emit(AssOp, t2, ValBool True,NIL)
            updateLabel lFin
            t <- freshTemp
            emit(Phi, t, SSA [(From lFalse t1), (From lTrue t2)], NIL)
            return t

        EAnd a expr1 expr2 -> do
            e1 <- genExpr expr1
            lFalse <- reserveLabel "l"
            lEnd <- reserveLabel "l"
            emit(IfOp NEm, e1, ValBool True, Label "l" lFalse)
            lSec <- genLabel "l"
            e2 <- genExpr expr2
            emit(IfOp NEm, e2, ValBool True, Label "l" lFalse)
            lTrue <- genLabel "l"
            t1 <- freshTemp
            emit(AssOp, t1, ValBool True, NIL)
            emit(GotoOp, Label "l" lEnd, NIL, NIL)
            updateLabel lFalse
            t2 <- freshTemp
            emit(AssOp, t2, ValBool False, NIL)
            updateLabel lEnd
            t <- freshTemp
            emit(Phi, t, SSA [(From lTrue t1), (From lFalse t2)], NIL)
            return t
        EOr a expr1 expr2 -> do
            e1 <- genExpr expr1
            lTrue <- reserveLabel "l"
            lEnd <- reserveLabel "l"
            emit(IfOp EQUm, e1, ValBool True, Label "l" lTrue)
            lSec <- genLabel "l"
            e2 <- genExpr expr2
            emit(IfOp EQUm, e2, ValBool True, Label "l"  lTrue)
            lFalse <- genLabel "l"
            t1 <- freshTemp
            emit(AssOp, t1, ValBool False, NIL)
            emit(GotoOp, Label "l" lEnd, NIL, NIL)
            updateLabel  lTrue
            t2 <- freshTemp
            emit(AssOp, t2, ValBool True ,NIL)
            updateLabel lEnd
            t <- freshTemp
            emit(Phi, t, SSA [(From lFalse t1), (From lTrue t2)], NIL)
            return t
        EApp a (Ident name) exprs -> do
              e <- mapM genExpr exprs
              params <- mapM emitArg e
              t <- freshTemp
              --emit(CallFun, t, Fun name, Args params)
              emit(CallOp, Fun name, t, NIL)
              return t
        --EClApp a ident1 ident2 exprs -> EClApp (f a) ident1 ident2 (map (fmap f) exprs)
    --    EArrLen a ident -> EArrLen (f a) ident


emitArg :: Argument -> StateT EnvMid IO (Argument)
emitArg arg = do
    emit(ParamOp, arg, NIL, NIL)
    return (arg)
