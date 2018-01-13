module Main where

import System.IO ( stdin, hGetContents, hPutStr, stderr )
import System.Environment ( getArgs, getProgName, getExecutablePath )
import System.Exit ( exitFailure, exitSuccess )
import Control.Monad (when)

import System.FilePath
import System.Process
import Control.Monad.IO.Class

import LexGrammar
import ParGrammar
import SkelGrammar
import PrintGrammar
import AbsGrammar


import FrontEnd
import IntermediateCode
import BackEnd

import ErrM

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: String -> Verbosity -> ParseFun (Program (Maybe (Int, Int))) -> FilePath -> IO ()
runFile file v p f = putStrLn f >> readFile f >>= run file v p

run :: String -> Verbosity -> ParseFun (Program (Maybe (Int, Int))) -> String -> IO ()
run file v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do hPutStr stderr "ERROR\n"
                          putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn s
                          exitFailure
           Ok  tree -> do putStrLn "\nParse Successful!"
                          --showTree v tree
                          frontEnd tree
                          controlGraph <- generateIntermediate tree
                          hPutStr stderr "OK\n"
                          generateLLVM file controlGraph
                          liftIO $ readProcess "llvm-as" [(dropExtension file) ++ ".ll"] ""
                          liftIO $ readProcess "llvm-link"
                            ["-o", (dropExtension file ++ ".bc"), (dropExtension file) ++ ".ll", "lib/runtime.bc"] ""
                          exitSuccess


showTree ::  Int -> (Program (Maybe (Int, Int))) -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> getContents >>= run (head args) 2 pProgram
    "-s":fs -> mapM_ (runFile (head args) 0 pProgram) fs
    fs -> mapM_ (runFile (head args) 2 pProgram) fs
