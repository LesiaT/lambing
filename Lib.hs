module Lib where
import Prelude hiding (lookup)
import System.IO ( hPutStrLn, stderr )
import Data.Map as Map
import AbsLambing
import PrintLambing
import Control.Monad.Except
import Control.Monad.State as MemS

data Var = VB (Maybe Bool) | VI (Maybe Int) | VS (Maybe String) | VLB [Bool] | VLI [Int] | VLS [String] | EmptyList

data Func = FunctionV [FunPar] [Decl] [Stmt] | FunctionT Typ [FunPar] [Decl] [Stmt] Exp

type VarMap = Map.Map Ident Var
type FuncMap = Map.Map Ident Func
-- pierwsza para to są zmienne globalne, druga - lokalne
-- przy wyszukiwaniu wartości zmiennej najpierw przeszukujemy
-- środowisko lokalne, i tylko po tym globalne, zatem lokalnie
-- zmienne mogą przesłaniać globalne
type Mem = (VarMap, FuncMap, VarMap, FuncMap, [String])
type MemState = ExceptT String (State Mem)

-- wypisywanie wyników działania programu
printAll' :: [String] -> IO()
printAll' [] = return ()
printAll' (s:ss) = do
  putStrLn s
  printAll' ss

printAll :: Either String [String] -> IO()
printAll es = do
  case es of
    Left s -> hPutStrLn stderr s
    Right ss -> printAll' ss

finallProg :: Mem -> [String]
finallProg (_, _, _, _, ss) = ss

-- Decl, Stmt, Exp

printType :: Typ -> String
printType TBool = "bool"
printType TInt = "int"
printType TStr = "string"
printType TListInt = "list<int>"
printType TListBool = "list<bool>"
printType TListStr = "list<string>"


varType :: Var -> String
varType (VB _) = "bool"
varType (VI _) = "int"
varType (VS _) = "string"
varType (VLB _) = "list<bool>"
varType (VLI _) = "list<int>"
varType (VLS _) = "list<string>"

mapBool :: LamBool -> Bool
mapBool BoolF = False
mapBool BoolT = True

varEq :: Var -> Var -> MemState Var
varEq (VB (Just v1)) (VB (Just v2)) = return (VB (Just (v1 == v2)))
varEq (VI (Just v1)) (VI (Just v2)) = return (VB (Just (v1 == v2)))
varEq (VS (Just v1)) (VS (Just v2)) = return (VB (Just (v1 == v2)))
varEq _ _ = throwError "Internal error"

varEnq :: Var -> Var -> MemState Var
varEnq (VB (Just v1)) (VB (Just v2)) = return (VB (Just (v1 /= v2)))
varEnq (VI (Just v1)) (VI (Just v2)) = return (VB (Just (v1 /= v2)))
varEnq (VS (Just v1)) (VS (Just v2)) = return (VB (Just (v1 /= v2)))
varEnq _ _ = throwError "Internal error"

-- pierwszy parametr to będzie >, <, >=, <=
intComp :: (Int -> Int -> Bool) -> Var -> Var -> MemState Var
intComp f (VI (Just v1)) (VI (Just v2)) = return (VB (Just (f v1 v2)))

--sprawdza czy indeks jest w zakresie długości listy
checkBound :: Exp -> Int -> Int -> MemState ()
checkBound ee ind len | ind < 0 = throwError $ "Negative index in " ++ ((render . prt 0) ee)
                      | ind > len =  throwError $ "Index is too large in " ++ ((render . prt 0) ee)
                      | otherwise = return ()

-- wypisywanie list, zmiennych..
showH :: (Show a) => [a] -> String
showH [] = ""
showH (x:xs) = " , " ++ show x ++ showH xs

show' :: (Show a) => [a] -> String
show' [] = "[]"
show' (x:xs) = "[" ++ (show x) ++ (showH xs) ++ "]"

showVar :: Var -> MemState String
showVar (VB (Just v)) = return (show v)
showVar (VI (Just v)) = return (show v)
showVar (VS (Just v)) = return v
showVar (VLB l) = return (show' l)
showVar (VLI l) = return (show' l)
showVar (VLS l) = return (show' l)
showVar _ = throwError "Undefined variable can't be printed"

-- sprawdza czy zgadzają się typy 2 zmiennych/zmiennej i konkretny typ/typR 
-- lub czy Var jest pustą listą

varTypeT :: Var -> Typ
varTypeT (VB _) = TBool
varTypeT (VI _) = TInt
varTypeT (VS _) = TStr
varTypeT (VLB _) = TListBool
varTypeT (VLI _) = TListInt
varTypeT (VLS _) = TListStr

varTypeMatch' :: Var -> Typ -> Bool
varTypeMatch' v t = (varTypeT v) == t

varTypeMatch :: Var -> Var -> Bool
varTypeMatch v1 v2 = (varTypeT v1) == (varTypeT v2)

funParamType :: FunPar -> Typ
funParamType (FunParam t _) = t
funParamType (FunParamR TBoolR _) = TBool
funParamType (FunParamR TIntR _) = TInt
funParamType (FunParamR TStrR _) = TStr
funParamType (FunParamR TListIntR _) = TListInt
funParamType (FunParamR TListStrR _) = TListStr
funParamType (FunParamR TListBoolR _) = TListBool

varTypeEmpty :: Var -> Var -> Maybe Var
varTypeEmpty (VLB _) (EmptyList) = Just (VLB [])
varTypeEmpty (VLI _) (EmptyList) = Just (VLI [])
varTypeEmpty (VLS _) (EmptyList) = Just (VLS [])
varTypeEmpty _ _ = Nothing

-- usuwa element z listy na konkretnej pozycji
delAtIndexI :: Int -> [Int] -> [Int] -> [Int]
delAtIndexI 0 l (x:xs) = l ++ xs
delAtIndexI n l (x:xs) = delAtIndexI (n-1) (l ++ [x]) xs

delAtIndexB :: Int -> [Bool] -> [Bool] -> [Bool]
delAtIndexB 0 l (x:xs) = l ++ xs
delAtIndexB n l (x:xs) = delAtIndexB (n-1) (l ++ [x]) xs

delAtIndexS :: Int -> [String] -> [String] -> [String]
delAtIndexS 0 l (x:xs) = l ++ xs
delAtIndexS n l (x:xs) = delAtIndexS (n-1) (l ++ [x]) xs

-- zmienia wartość n-tego elementu listy na podaną
replaceAtIndexI :: Int -> Int -> [Int] -> [Int] -> [Int]
replaceAtIndexI 0 item l (x:xs) = l ++ [item] ++ xs
replaceAtIndexI n item l (x:xs) = replaceAtIndexI (n-1) item (l ++ [x]) xs

replaceAtIndexB :: Int -> Bool -> [Bool] -> [Bool] -> [Bool]
replaceAtIndexB 0 item l (x:xs) = l ++ [item] ++ xs
replaceAtIndexB n item l (x:xs) = replaceAtIndexB (n-1) item (l ++ [x]) xs

replaceAtIndexS :: Int -> String -> [String] -> [String] -> [String]
replaceAtIndexS 0 item l (x:xs) = l ++ [item] ++ xs
replaceAtIndexS n item l (x:xs) = replaceAtIndexS (n-1) item (l ++ [x]) xs

-- czy zmienna nie była zainicjowana?
checkIfEmpty :: Var -> Bool
checkIfEmpty (VB Nothing) = True
checkIfEmpty (VI Nothing) = True
checkIfEmpty (VS Nothing) = True
checkIfEmpty _ = False

-- przy zakończeniu funkcji nadpisuje wartości przekazane prze zmienne
funModify :: VarMap -> FuncMap -> [(Maybe Ident, Ident)] -> MemState ()
funModify m1' m2' [] = modify ( \(m1, m2, _, _, p) -> (m1, m2, m1', m2', p))
funModify m1' m2' ((Nothing, _):ids) = funModify m1' m2' ids
funModify m1' m2' ((Just id, id'):ids) = do
  (m1, _, m1'', _,  _) <- MemS.get
  case (lookup id' m1'') of
    Nothing -> throwError $ "internal error"
    Just v -> do
      case (lookup id m1') of
        Nothing -> do
          case (lookup id m1) of
            Just _ -> modify (\(m1, m2, m1', m2', p) -> (insert id v m1, m2, m1', m2', p)) >> funModify m1' m2' ids
            Nothing -> throwError $ "Internal error"
        Just _ -> funModify (insert id v m1') m2' ids

-- przy wejściu do funkcji aktualizuje lokalne środowisko zmiennych
setLocalEnv :: [(Maybe Ident, Ident)] -> VarMap -> MemState ()
setLocalEnv [] _ = return ()
setLocalEnv ((_, id):ids) m = do
  case (lookup id m) of
    Nothing -> throwError $ "Internal error"
    Just v -> modify (\(m1, m2, m1', m2', p) -> (m1, m2, insert id v m1', m2', p)) >> setLocalEnv ids m

refreshMem :: VarMap -> FuncMap -> MemState ()
refreshMem m1_old m2_old = do
  (m1, m2, m1', m2', p) <- MemS.get
  modify(\(m1, m2, _, _, p) -> (m1, m2, m1_old, m2_old, p)) >>
    mapM_ overwriteV (toList m1') >> mapM_ overwriteF (toList m2')

overwriteV :: (Ident,Var) -> MemState ()
overwriteV (id,v) = modify(\(m1, m2, m1', m2', p) -> (m1, m2, insert id v m1', m2', p))

overwriteF :: (Ident,Func) -> MemState ()
overwriteF (id,f) = modify(\(m1, m2, m1', m2', p) -> (m1, m2, m1', insert id f m2', p))
