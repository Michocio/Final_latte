module Optimisations where

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
import TypesStuff
import IntermediateEnv
import Misc

--type SimpleBlock = (Argument, [Tuple])
--type ControlFlow = (Argument, [Argument])

replaceBy :: [Tuple] ->  (Argument, Argument) -> [Tuple]
replaceBy  code  (src, dst) =
    map (changeRegs (src, dst)) code

changeRegs :: (Argument, Argument) -> Tuple -> Tuple
changeRegs (src, dst) (AssOp, res, arg1, NIL) =
    (AssOp, res, isDesiredArg src dst arg1 , NIL)
changeRegs (src, dst) (Alloca t, arg1, res, arg3) =
    (Alloca t, arg1, res, arg3)
changeRegs (src, dst) (Phi, res, SSA xs, a) =
    constExpr (Phi, res, SSA $ map (\(From b x) -> From b (isDesiredArg src dst x)) xs, a)
changeRegs (src, dst) (ParamOp, arg1, arg2, arg3) =
    constExpr (ParamOp, isDesiredArg src dst  arg1, isDesiredArg src dst arg2, isDesiredArg src dst arg3)
changeRegs (src, dst) (op, arg1, arg2, arg3) =
    constExpr (op, isDesiredArg src dst  arg1, isDesiredArg src dst arg2, isDesiredArg src dst arg3)

isDesiredArg :: Argument -> Argument -> Argument -> Argument
isDesiredArg y z x = if(x==y) then z else x

addLife :: Argument -> [Argument]
addLife NIL = []
addLife a@(Var x y z i) = [a]
addLife a@(Reg x) = [a]
addLife x = []

removeDeadUsage :: [Argument] -> Tuple -> Maybe Tuple
removeDeadUsage ok (AssOp, res, arg1, arg3) =
    if(res==arg1) then Nothing
    else
        if ((elem res ok) == False) then Nothing
        else (Just (AssOp, res, arg1, arg3))
--removeDeadUsage ok (Alloca z, arg1, res, arg3) =
--    if ((elem arg1 ok) == False) then Nothing
--    else (Just (Alloca z, arg1, res, arg3))
removeDeadUsage ok (Phi, res, phis, arg3) =
    if ((elem res ok) == False) then Nothing
    else (Just (Phi, res, phis, arg3))
removeDeadUsage a b = Just b

aliveVar :: ([Argument], [Argument]) -> [Tuple] -> StateT EnvMid IO ([Argument], [Argument])
aliveVar  (declared, used) [] = return (nub declared, nub used)
aliveVar (declared, used) ((AssOp, src, dst, NIL):xs) = aliveVar (declared++[dst], used) xs
aliveVar (declared, used) ((Alloca _, dst, NIL, NIL):xs)= aliveVar (declared++[dst], used) xs
aliveVar (declared, used) ((Phi, dst, SSA phis, NIL):xs) = let
    filtered = filter (\(From b x) -> x/=dst) phis in
        aliveVar (declared ++ [dst], (map (\(From b x) -> x) filtered) ++ used) xs
--aliveVar (declared, used) ((CallFun, t, name, Args params):xs) = let
--    filtered = filter ifVar params in
--        aliveVar (declared, (filtered) ++ used) xs
aliveVar (declared, used) ((op, a1, a2, a3):xs)=
    aliveVar (declared, used ++ (addLife a1)++ (addLife a2)++ (addLife a3)) xs

doOpt :: [[Tuple]] ->  StateT EnvMid IO [[Tuple]]
doOpt code = do
    new_code <- constOpt code
    new_code_ <- copyOpt new_code
    com <- commonExpr new_code_
    if(com /= code) then doOpt com
    else return new_code_

commonExpr ::  [[Tuple]] ->  StateT EnvMid IO [[Tuple]]
commonExpr code = do
    pr <- return $ foldr (++) [] code
    m <- commonsSet pr M.empty
    return $ map (map (linkCommon m)) code

linkCommon :: (M.Map Tuple Argument) -> Tuple ->  Tuple
linkCommon m t@(op, res, a1, a2) = do
    case (M.lookup (op, NIL, a1, a2) m) of
        (Nothing) -> t
        (Just x) -> do
            if(x==res) then t
            else (AssOp, res, x, NIL)

commonsSet :: [Tuple] -> (M.Map Tuple Argument) -> StateT EnvMid IO (M.Map Tuple Argument)
commonsSet [] m = return m
commonsSet (x@(AddOp, res, a, b):xs) m = do
    if(isJust $ M.lookup x m) then return m
    else do
        commonsSet xs (M.insert (AddOp, NIL, a, b) res m)
commonsSet (x@(MulOp, res, a, b):xs) m = do
    if(isJust $ M.lookup x m) then return m
    else do
        commonsSet xs (M.insert (MulOp, NIL, a, b) res m)
commonsSet (x@(SubOp, res, a, b):xs) m = do
    if(isJust $ M.lookup x m) then return m
    else do
        commonsSet xs (M.insert (SubOp, NIL, a, b) res m)
commonsSet (x@(DivOp, res, a, b):xs) m = do
    if(isJust $ M.lookup x m) then return m
    else do
        commonsSet xs (M.insert (DivOp, NIL, a, b) res m)
commonsSet (x:xs) m = commonsSet xs m

constOpt :: [[Tuple]] ->  StateT EnvMid IO [[Tuple]]
constOpt code = do
    consts <- return $ foldr (++) [] (map (map constAss) code)
    pary <- return $ map (fromJust) (filter (isJust) consts)
    blocks <- return $ map (correctCode pary) code
    return blocks


copyOpt :: [[Tuple]] ->  StateT EnvMid IO [[Tuple]]
copyOpt code = do
    copies <- return $ foldr (++) [] (map (map copyAss) code)
    pary <- return $ map (fromJust) (filter (isJust) copies)
    blocks <- return $ map (correctCode pary) code
    return blocks

copyAss :: Tuple -> Maybe (Argument, Argument)
copyAss (AssOp, src, ValStr s, _) = Nothing
copyAss (AssOp, src, dst, _) = Just (src, dst)
copyAss _ = Nothing


correctCode :: [(Argument, Argument)] -> [Tuple] ->  [Tuple]
correctCode [] code = replaceBy code (NIL, NIL)
correctCode (x:xs) code =
    correctCode xs (replaceBy code x)

constExpr :: Tuple -> Tuple
constExpr (Phi, res, SSA xs, o) =
    let (From b x) = head xs in
       if(any (\t -> t == False) $ map ((\(From _ y) -> x==y)) xs) then
            (Phi, res, SSA xs, o)
        else
            (AssOp, res, x, NIL)
constExpr (AndOp, res, ValBool i1, ValBool i2) =
    (AssOp, res, ValBool (i1 && i2), NIL)
constExpr (OrOp, res, ValBool i1, ValBool i2) =
    (OrOp, res, ValBool (i1 || i2), NIL)
constExpr (AddOp, res, ValInt i1, ValInt i2) =
    (AssOp, res, ValInt (i1 + i2), NIL)
constExpr (SubOp, res, ValInt i1, ValInt i2) =
    (AssOp, res, ValInt (i1 - i2), NIL)
constExpr (DivOp, res, ValInt i1, ValInt i2) =
    (AssOp, res, ValInt (div i1 i2), NIL)
constExpr (MulOp, res, ValInt i1, ValInt i2) =
    (AssOp, res, ValInt (i1 * i2), NIL)
constExpr (ModOp, res, ValInt i1, ValInt i2) =
    (AssOp, res, ValInt (mod i1 i2), NIL)
constExpr (NegOp, res, ValInt i1, _) =
    (AssOp, res, ValInt ((-1) *i1), NIL)
constExpr (NotOp, res, ValBool i1, _) =
    (AssOp, res, ValBool (not i1), NIL)
constExpr (IfOp how, a1, a2, l) =
    if(isConst a1 && isConst a2) then
        if(ifInt a1) then
            if((compFun how) (takeInt a1) (takeInt a2)) then
                (GotoOp, l, NIL, NIL)
            else
                (AssOp, ValInt 7, ValInt 7, NIL)
        else
            if(ifBool a1) then
                if((compFun how) (takeBool a1) (takeBool a2)) then
                    (GotoOp, l, NIL, NIL)
                else
                    (AssOp, ValInt 7, ValInt 7, NIL)
            else
                (IfOp how, a1, a2, l)
    else
        (IfOp how, a1, a2, l)
constExpr x = x

ifInt (ValInt i) = True
ifInt _ = False
ifBool (ValBool b) = True
ifBool _ = False
ifStr (ValStr s) = True
ifStr _ = False

takeInt (ValInt i) = i
takeBool (ValBool b) = b
takeStr (ValStr s) = s



compFun ::(Ord a) => CmpOp -> (a->a->Bool)
compFun LTHm = (<)
compFun LEm = (<=)
compFun GTHm = (>)
compFun GEm = (>=)
compFun EQUm = (==)
compFun NEm = (/=)

--zwijanie stalych
constAss :: Tuple -> Maybe (Argument, Argument)
constAss (AssOp, src, dst, _) =
    if(isConst dst) then Just (src, dst)
    else Nothing
constAss (NegOp, src, ValInt i1, _) =
    Just (src, ValInt ((-1) *i1))
constAss _ = Nothing

isConst :: Argument -> Bool
isConst (ValInt _) = True
isConst (ValBool _) = True
isConst (ValStr _) = False
isConst (ValVoid) = True
isConst _ = False
