module ExecStmt where
import Lib
import Prelude hiding (lookup)
import Data.Map as Map
import AbsLambing
import PrintLambing
import Control.Monad.Except
import Control.Monad.State as MemS

-- wykonanie deklaracji

-- pierwszy parametr oznacza że to są zmienne globalne
execDeclsM :: Bool -> [Decl] -> MemState ()
execDeclsM _ [] = return ()
execDeclsM b (d:ds) = execDeclM b d >> execDeclsM b ds

insertVar :: Bool -> Ident -> Var -> MemState ()
insertVar True id EmptyList = do
  (m1, _, _, _, _) <- MemS.get
  case (lookup id m1) of
    Just (VLB _) -> modify (\ (m1, m2, m1', m2',p) -> (insert id (VLB []) m1, m2, m1', m2', p))
    Just (VLI _) -> modify (\ (m1, m2, m1', m2',p) -> (insert id (VLI []) m1, m2, m1', m2', p))
    Just (VLS _) -> modify (\ (m1, m2, m1', m2',p) -> (insert id (VLS []) m1, m2, m1', m2', p))
    _ -> throwError "Internal error"
insertVar False id EmptyList = do
  (_, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB _) -> modify (\ (m1, m2, m1', m2',p) -> (m1, m2, insert id (VLB []) m1', m2', p))
    Just (VLI _) -> modify (\ (m1, m2, m1', m2',p) -> (m1, m2, insert id (VLI []) m1', m2', p))
    Just (VLS _) -> modify (\ (m1, m2, m1', m2',p) -> (m1, m2, insert id (VLS []) m1', m2', p))
    _ -> throwError "Internal error"
insertVar True id v = modify (\ (m1, m2, m1', m2',p) -> (insert id v m1, m2, m1', m2', p))
insertVar False id v = modify (\ (m1, m2, m1', m2',p) -> (m1, m2, insert id v m1', m2', p))

emptyVar :: Typ -> Var
emptyVar t =
  case t of
    TInt -> (VI Nothing)
    TBool -> (VB Nothing)
    TStr -> (VS Nothing)
    TListInt -> (VLI [])
    TListBool -> (VLB [])
    TListStr -> (VLS [])

lookForVar :: Bool -> Typ -> Ident -> MemState ()
lookForVar True t id = do
  (m1, _, _, _, _) <- MemS.get
  case (lookup id m1) of
    Nothing -> insertVar True id (emptyVar t)
    _ -> throwError $ "Variable " ++ show id ++ " has been declared already"
lookForVar False t id = do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Nothing -> do
      case (lookup id m1) of
        Nothing -> insertVar False id (emptyVar t)
        _ -> throwError $ "Global variable " ++ ((render . prt 0) id) ++ " exists already"
    _ -> throwError $ "Variable " ++ show id ++ " has been declared already"

insertFun :: Bool -> Ident -> Func -> MemState ()
insertFun True id f = modify (\ (m1, m2, m1', m2',p) -> (m1, insert id f m2, m1', m2', p))
insertFun False id f = modify (\ (m1, m2, m1', m2',p) -> (m1, m2, m1', insert id f m2', p))

lookForFun :: Bool -> Ident -> Maybe (Typ, Exp) -> [FunPar] -> [Decl] -> [Stmt] -> MemState ()
lookForFun True id te fp ds ss = do
  (_, m2, _, _, _) <- MemS.get
  case (lookup id m2) of
    Nothing -> do
      case te of
        Nothing -> insertFun True id (FunctionV fp ds ss)
        Just (t, e) -> insertFun True id (FunctionT t fp ds ss e)
    _ -> throwError $ "Function " ++ show id ++ " has been declared already"
lookForFun False id te fp ds ss = do
  (_, m2, _, m2', _) <- MemS.get
  case (lookup id m2') of
    Nothing -> do
      case (lookup id m2) of
        Nothing -> do
          case te of
            Nothing -> insertFun False id (FunctionV fp ds ss)
            Just (t, e) -> insertFun False id (FunctionT t fp ds ss e)
        _ -> throwError $ "Global function " ++ ((render . prt 0) id) ++ " exists already"
    _ -> throwError $ "Function " ++ show id ++ " has been declared already"

declVar :: Bool -> Typ -> Ident -> MemState ()
declVar True t id = do
  (m1, _, _, _, _) <- MemS.get
  lookForVar True t id
declVar False t id = do
  (_, _, m1', _, _) <- MemS.get
  lookForVar False t id

declVars :: Bool -> Typ -> [Ident] -> MemState ()
declVars _ t [] = return ()
declVars b t (id:ids) = declVar b t id >> declVars b t ids

execDeclM :: Bool -> Decl -> MemState ()
execDeclM b (DeclD t m@(id:ids)) = declVars b t m
execDeclM b (DeclWithV t i e) = declVar b t i >> execStmtM (SAss i e)
execDeclM True (DeclFun (Func TVoid i fp (FuncBody ds ss))) = do
  (_, m2, _, _, _) <- MemS.get
  lookForFun True i Nothing fp ds ss
execDeclM False (DeclFun (Func TVoid i fp (FuncBody ds ss))) = do
  (_, _, _, m2', _) <- MemS.get
  lookForFun False i Nothing fp ds ss
execDeclM True (DeclFun (FuncT t i fp (FuncBodyWithR ds ss e))) = do
  (_, m2, _, _, _) <- MemS.get
  lookForFun True i (Just (t, e)) fp ds ss
execDeclM False (DeclFun (FuncT t i fp (FuncBodyWithR ds ss e))) = do
  (_, _, _, m2', _) <- MemS.get
  lookForFun False i (Just (t, e)) fp ds ss

-- wykonanie instrukcji

-- Zamienia wartość listy na konkretnej pozycji, pierwszyparametr działa tak samo jak w decl
exchList :: Bool -> Var -> Exp -> Int -> Ident -> MemState ()
exchList b vl e n id = do
  case vl of
    (VLS l) -> do
      (VS (Just v)) <- evalExp e
      insertVar b id (VLS (replaceAtIndexS n v [] l))
    (VLB l) -> do
      (VB (Just v)) <- evalExp e
      insertVar b id (VLB (replaceAtIndexB n v [] l))
    (VLI l) -> do
      (VI (Just v)) <- evalExp e
      insertVar b id (VLI (replaceAtIndexI n v [] l))
    _ -> throwError $ "Internal error 1"

assVar :: Bool -> Ident -> Var -> Exp -> MemState ()
assVar b id v e = do
  v' <- evalExp e
  insertVar b id v'

-- sprawdza czy indeks nie jest spoza listy i nadpisuje element
checkAndExch :: Bool -> Ident -> Exp -> Exp -> Var -> Int -> Int -> MemState ()
checkAndExch b id e1 e2 v l ind = checkBound (EListVar id e1) ind l >> exchList b v e2 ind id

execStmtsM :: [Stmt] -> MemState ()
execStmtsM [] = return ()
execStmtsM (s:ss) = execStmtM s >> execStmtsM ss

execStmtM :: Stmt -> MemState ()
execStmtM (SAss id e) = do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Nothing -> do
      case (lookup id m1) of
        Nothing -> throwError "Internal error 2"
        Just v -> assVar True id v e
    Just v -> assVar False id v e

execStmtM (SListAss id e1 e2) = do
  (VI (Just ind)) <- evalExp e1
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB l) -> checkAndExch False id e1 e2 (VLB l) (length l - 1) ind
    Just (VLI l) -> checkAndExch False id e1 e2 (VLI l) (length l - 1) ind
    Just (VLS l) -> checkAndExch False id e1 e2 (VLS l) (length l - 1) ind
    Nothing -> do
      case (lookup id m1) of
        Just (VLB l) -> checkAndExch True id e1 e2 (VLB l) (length l - 1) ind
        Just (VLI l) -> checkAndExch True id e1 e2 (VLI l) (length l - 1) ind
        Just (VLS l) -> checkAndExch True id e1 e2 (VLS l) (length l - 1) ind
        _ -> throwError "Internal error 3"
    _ -> throwError "Internal error 4"
execStmtM (SListClear id) = execStmtM (SAss id (EListEmpty))
execStmtM (SListDelete id e) = do
  (VI (Just ind)) <- evalExp e
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB l) -> checkBound (EListVar id e) ind (length l - 1) >>
                    insertVar False id (VLB (delAtIndexB ind [] l))
    Just (VLI l) -> checkBound (EListVar id e) ind (length l - 1) >>
                    insertVar False id (VLI (delAtIndexI ind [] l))
    Just (VLS l) -> checkBound (EListVar id e) ind (length l - 1) >>
                    insertVar False id (VLS (delAtIndexS ind [] l))
    Nothing -> do
      case (lookup id m1) of
        Just (VLB l) -> checkBound (EListVar id e) ind (length l - 1) >>
                        insertVar True id (VLB (delAtIndexB ind [] l))
        Just (VLI l) -> checkBound (EListVar id e) ind (length l - 1) >>
                        insertVar True id (VLI (delAtIndexI ind [] l))
        Just (VLS l) -> checkBound (EListVar id e) ind (length l - 1) >>
                        insertVar True id (VLS (delAtIndexS ind [] l))
        _ -> throwError "Internal error 5"
    _ -> throwError "Internal error 6"
execStmtM ee@(SListNew id e) = do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB l) -> do
      (VB (Just v)) <- evalExp e
      insertVar False id (VLB (l ++ [v]))
    Just (VLI l) -> do
      (VI (Just v)) <- evalExp e
      insertVar False id (VLI (l ++ [v]))
    Just (VLS l) -> do
      (VS (Just v)) <- evalExp e
      insertVar False id (VLS (l ++ [v]))
    Nothing -> do
      case (lookup id m1) of
        Just (VLB l) -> do
          (VB (Just v)) <- evalExp e
          insertVar True id (VLB (l ++ [v]))
        Just (VLI l) -> do
          (VI (Just v)) <- evalExp e
          insertVar True id (VLI (l ++ [v]))
        Just (VLS l) -> do
          (VS (Just v)) <- evalExp e
          insertVar True id (VLS (l ++ [v]))
        _ -> throwError $ "Internal error 7" ++ ((render . prt 0) ee) 
    _ -> throwError "Internal error 8"

execStmtM (SPrint e) = do
  ev <- evalExp e >>= showVar
  modify (\ (m1, m2, m1', m2', p) -> (m1, m2, m1', m2', p ++ [ev]))

execStmtM (SIfS e s) = do
  (VB (Just v)) <- evalExp e
  if (v) then execStmtsM s else return()
execStmtM (SIfElS e1 s1 e2 s2) = do
  (VB (Just v1)) <- evalExp e1
  (VB (Just v2)) <- evalExp e2
  if (v1) then execStmtsM s1 else if (v2) then execStmtsM s2 else return()
execStmtM (SIfElL e1 s1 e2 s2 s3) = do
  (VB (Just v1)) <- evalExp e1
  (VB (Just v2)) <- evalExp e2
  if (v1) then execStmtsM s1 else if (v2) then execStmtsM s2 else execStmtsM s3
execStmtM (SIfL e s1 s2) = do
  (VB (Just v)) <- evalExp e
  if (v) then execStmtsM s1 else execStmtsM s2
execStmtM st@(SWhile e s) = do
  (VB (Just v)) <- evalExp e
  if (v) then do
    execStmtsM s
    execStmtM st
  else return()

execStmtM st@(SCallFunE id) = do
  (_, m2, m1', m2', _) <- MemS.get
  case (lookup id m2') of
    Just (FunctionV [] ds ss) -> modify (\(m1,m2,_,_,p) -> (m1, m2, Map.empty, Map.empty,p)) >> runFunDecl ds >> refreshMem m1' m2' >> runFunStmt ss [] >>= funModify m1' m2'
    Nothing -> do
      case (lookup id m2) of
        Just (FunctionV [] ds ss) -> modify (\(m1,m2,_,_,p) -> (m1, m2, Map.empty, Map.empty,p)) >> runFunDecl ds >> refreshMem m1' m2' >> runFunStmt ss [] >>= funModify m1' m2'
        _ -> throwError "Internal error 9"
    _ -> throwError "Internal error 10"

execStmtM st@(SCallFun id exps) = do
  (_, m2, m1', m2', _) <- MemS.get
  case (lookup id m2') of
    Just (FunctionV fp ds ss) -> execFun st exps fp ds ss ([], Map.empty) >>= funModify m1' m2'
    Nothing -> do
      case (lookup id m2) of
        Just (FunctionV fp ds ss) -> execFun st exps fp ds ss ([], Map.empty) >>= funModify m1' m2'
        _ -> throwError "Internal error 11"
    _ -> throwError "Internal error 12"


-- nadpisujemy lokalne środowisko, wykonujemy ciało funkcji
-- przywracamy poprzednie lokalne środowisko i zmieniamy wszystkie wartości w pamięci które były przekazane przez zmienne
execFun :: Stmt -> [Exp] -> [FunPar] -> [Decl] -> [Stmt] -> ([(Maybe Ident, Ident)], VarMap) -> MemState [(Maybe Ident, Ident)]
execFun st [] [] ds ss (re, m) = do
  (m1,m2,m1',m2',p) <- MemS.get
  modify (\(m1,m2,_,_,p) -> (m1, m2, Map.empty, Map.empty,p)) >> setLocalEnv re m >> runFunDecl ds >> refreshMem m1' m2' >> runFunStmt ss re
execFun st (exp:exps) (fp:fps) ds ss (re, m) = parMatch re m exp fp >>= execFun st exps fps ds ss
execFun st _ _ _ _ _ = throwError $ "Internal error 13"

parMatch :: [(Maybe Ident, Ident)] -> VarMap -> Exp -> FunPar -> MemState ([(Maybe Ident, Ident)], VarMap)
parMatch l m exp fp@(FunParam _ id') = do
  v <- evalExp exp
  return ((l ++ [(Nothing, id')]), insert id' v m)
parMatch l m exp@(EVar id) fp@(FunParamR _ id') = do
  v <- evalExp exp
  return ((l ++ [(Just id, id')]), insert id' v m)
-- TODO czy tutaj na pewno wywalo się jak będą dwa argumenty o tej zamej nazwie

runFunDecl :: [Decl] -> MemState ()
runFunDecl ds = execDeclsM False ds

runFunStmt :: [Stmt] -> [(Maybe Ident, Ident)] -> MemState [(Maybe Ident, Ident)]
runFunStmt ss re = execStmtsM ss >> return re


-- obliczenia wyrażeń
-- z listy Exp tworzy listę potrzbnego typu, jeśli któryś Exp ma niezgodny typ wywala się
evalListB :: [Bool] -> [Exp] -> MemState Var
evalListB bs [] = return (VLB bs)
evalListB bs (e:es) = do
  (VB (Just v)) <- evalExp e
  evalListB (bs ++ [v]) es

evalListI :: [Int] -> [Exp] -> MemState Var
evalListI is [] = return (VLI is)
evalListI is (e:es) = do
  (VI (Just v)) <- evalExp e
  evalListI (is ++ [v]) es

evalListS :: [String] -> [Exp] -> MemState Var
evalListS ss [] = return (VLS ss)
evalListS ss (e:es) = do
  (VS (Just v)) <- evalExp e
  evalListS (ss ++ [v]) es


evalExp :: Exp -> MemState Var
evalExp (EOpA e1 op e2) = do
  (VB (Just v1)) <- evalExp e1
  (VB (Just v2)) <- evalExp e2
  case op of
    OAnd -> return (VB (Just (v1 && v2)))
    OOr -> return (VB (Just (v1 || v2)))
evalExp (EOpB e1 op e2) = do
  v1 <- evalExp e1
  v2 <- evalExp e2
  case op of
    OEq -> varEq v1 v2
    OEnq -> varEnq v1 v2
    OLt -> intComp (<) v1 v2
    OGt -> intComp (>) v1 v2
    OLe -> intComp (<=) v1 v2
    OGe -> intComp (>=) v1 v2
evalExp (EOpC e1 op e2) = do
  (VI (Just v1)) <- evalExp e1
  (VI (Just v2)) <- evalExp e2
  case op of
    OPlus -> return (VI (Just (v1 + v2)))
    OMinus -> return (VI (Just (v1 - v2)))
evalExp ee@(EOpD e1 op e2) = do
  (VI (Just v1)) <- evalExp e1
  (VI (Just v2)) <- evalExp e2
  case op of
    OMul -> return (VI (Just (v1 * v2)))
    ODiv -> do
      case v2 of
        0 -> throwError $ "Dividing by 0 in " ++ ((render . prt 0) ee)
        _ -> return (VI (Just (div v1 v2)))
evalExp (EVar id) =  do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Nothing -> do
      case (lookup id m1) of
        Just (VB Nothing) -> throwError $ "Variable " ++ show id ++ " hasn't been initialized"
        Just (VI Nothing) -> throwError $ "Variable " ++ show id ++ " hasn't been initialized"
        Just (VS Nothing) -> throwError $ "Variable " ++ show id ++ " hasn't been initialized"
        Just v -> return v
        Nothing -> throwError "Internal error 14"
    Just (VB Nothing) -> throwError $ "Variable " ++ show id ++ " hasn't been initialized"
    Just (VI Nothing) -> throwError $ "Variable " ++ show id ++ " hasn't been initialized"
    Just (VS Nothing) -> throwError $ "Variable " ++ show id ++ " hasn't been initialized"
    Just v -> return v
evalExp ee@(EListVar id e) = do
  (VI (Just ind)) <- evalExp e
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB l) -> checkBound ee ind (length l - 1) >> return (VB (Just (l !! ind)))
    Just (VLI l) -> checkBound ee ind (length l - 1) >> return (VI (Just (l !! ind)))
    Just (VLS l) -> checkBound ee ind (length l - 1) >> return (VS (Just (l !! ind)))
    Nothing -> do
      case (lookup id m1) of
        Just (VLB l) -> checkBound ee ind (length l - 1) >> return (VB (Just (l !! ind)))
        Just (VLI l) -> checkBound ee ind (length l - 1) >> return (VI (Just (l !! ind)))
        Just (VLS l) -> checkBound ee ind (length l - 1) >> return (VS (Just (l !! ind)))
        _ -> throwError "Internal error 15"
    _ -> throwError "Internal error 16"
evalExp (EListSize id) = do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB l) -> return (VI (Just (length l)))
    Just (VLI l) -> return (VI (Just (length l)))
    Just (VLS l) -> return (VI (Just (length l)))
    Nothing -> do
      case (lookup id m1) of
        Just (VLB l) -> return (VI (Just (length l)))
        Just (VLI l) -> return (VI (Just (length l)))
        Just (VLS l) -> return (VI (Just (length l)))
        _ -> throwError "Internal error 17"
    _ -> throwError "Internal error 18"

evalExp (EInt i) = return (VI (Just (fromIntegral i)))
evalExp (EIntM i) = return (VI (Just (fromIntegral (-i))))
evalExp (EString s) = return (VS (Just s))
evalExp (EBool BoolT) = return (VB (Just (mapBool BoolT)))
evalExp (EBool BoolF) = return (VB (Just (mapBool BoolF)))

evalExp (EListEmpty) = return (EmptyList)
evalExp ee@(EListOfV l@(e:es)) = do
  e' <- evalExp e
  case e' of
    (VB _) -> evalListB [] l
    (VI _) -> evalListI [] l
    (VS _) -> evalListS [] l
    _ -> throwError "Internal error 19"

evalExp ee@(EFunE id) = do
  (_, m2, m1', m2', _) <- MemS.get
  case (lookup id m2') of
    Just (FunctionT t [] ds ss e) -> modify (\(m1,m2,_,_,p) -> (m1, m2, Map.empty, Map.empty,p)) >> runFunDecl ds >> refreshMem m1' m2' >> runFunStmt ss [] >>= getRes e >>= funModifyV m1' m2'>>= return
    Nothing -> do
      case (lookup id m2) of
        Just (FunctionT t [] ds ss e) -> modify (\(m1,m2,_,_,p) -> (m1, m2, Map.empty, Map.empty,p)) >> runFunDecl ds >> refreshMem m1' m2' >> runFunStmt ss [] >>= getRes e >>= funModifyV m1' m2' >>= return
        Nothing -> throwError "Internal error 20"

evalExp ee@(EFun id exps) = do
  (_, m2, m1', m2', _) <- MemS.get
  case (lookup id m2') of
    Just (FunctionT t fp ds ss e) -> execFunV ee t exps fp ds ss e ([], Map.empty) >>= funModifyV m1' m2' >>= return
    Nothing -> do
      case (lookup id m2) of
        Just (FunctionT t fp ds ss e) -> execFunV ee t exps fp ds ss e ([], Map.empty) >>= funModifyV m1' m2' >>= return
        Nothing -> throwError "Internal error 21"

funModifyV :: VarMap -> FuncMap -> ([(Maybe Ident, Ident)], Var) -> MemState Var
funModifyV vm fm (re, v) = funModify vm fm re >> return v

execFunV :: Exp -> Typ -> [Exp] -> [FunPar] -> [Decl] -> [Stmt] -> Exp -> ([(Maybe Ident, Ident)], VarMap) -> MemState ([(Maybe Ident, Ident)], Var)
execFunV ee t [] [] ds ss e (re, m) = do
  (m1,m2,m1',m2',p) <- MemS.get
  modify (\(m1,m2,_,_,p) -> (m1, m2, Map.empty, Map.empty,p)) >> setLocalEnv re m >> runFunDecl ds >> refreshMem m1' m2' >> runFunStmt ss re >>= getRes e
execFunV ee t (exp:exps) (fp:fps) ds ss e (re, m) = parMatch re m exp fp >>= execFunV ee t exps fps ds ss e


getRes :: Exp -> [(Maybe Ident, Ident)] -> MemState ([(Maybe Ident, Ident)], Var)
getRes e re = do
  v <- evalExp e
  return (re, v)
