module Main where
import Lib
import ExecStmt
import TypeChecker
import Data.Map as Map
import AbsLambing
import LexLambing
import ParLambing
import Control.Monad.Except
import Control.Monad.State
import System.IO ( stdin, hGetContents, hPutStrLn, stderr )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )
import ErrM

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> hGetContents stdin >>= getTree 2 pProgr
    fs -> mapM_ (runFile 2 pProgr) fs


-- Część odpowiadająca za wczytania wejścia i sparsowania go do drzewa
type Parser a = StateT [Char] Maybe a
type ParseFun a = [Token] -> Err a
type Verbosity = Int

myLLexer = myLexer

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then hPutStrLn stderr s else return ()

runFile :: Verbosity -> ParseFun Progr -> FilePath -> IO ()
runFile v p f = readFile f >>= getTree v p

getTree :: Verbosity -> ParseFun Progr -> String -> IO ()
getTree v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do hPutStrLn stderr "\nParse Failed...\n"
                          hPutStrLn stderr s
                          exitFailure
           Ok  tree -> do interpret tree
                          exitSuccess

-- Część interpretacji
interpret :: Progr -> IO ()
interpret p@(Program d1 d2 s) = printAll $ evalState (runExceptT ((typeCheckerM p >> execDeclsM True d1 >> execDeclsM False d2 >> execStmtsM s) >> gets finallProg)) (Map.empty, Map.empty, Map.empty, Map.empty, [])
