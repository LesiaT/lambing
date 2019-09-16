module TypeChecker where
import Prelude hiding (lookup)
import Lib
import ExecStmt
import Data.Map as Map
import AbsLambing
import PrintLambing
import Control.Monad.Except
import Control.Monad.State as MemS


typeCheckerM :: Progr -> MemState ()
typeCheckerM (Program d1 d2 s) = (declsCheckT True d1 [] >> declsCheckT False d2 [] >> stmtsCheckT s) >> modify (\(_, _, _, _, _) -> (Map.empty, Map.empty, Map.empty, Map.empty, []))

-- Decl
expTypeIsGood :: Typ -> Exp -> MemState ()
expTypeIsGood t e = do
  r <- expCheckT t e
  if r then return ()
  else throwError $ "Type " ++ printType t ++ " expected in " ++ ((render . prt 0) e)

checkAllFunT :: [Ident] -> MemState ()
checkAllFunT [] = return ()
checkAllFunT (f:fs) = do
  (_, m2, _, m2', _) <- MemS.get
  case (lookup f m2') of
    Nothing -> do
      case (lookup f m2) of
        Nothing -> throwError "Internal error"
        Just (FunctionV fp ds ss) -> do
          mem <- funCheckT fp ds ss
          modify (\_ -> mem)
        Just (FunctionT t fp ds ss e) -> do
          mem <- funCheckT fp ds ss
          expectedExpType t e >> modify (\_ -> mem)
    Just (FunctionV fp ds ss) -> do
      mem <- funCheckT fp ds ss
      modify (\_ -> mem)
    Just (FunctionT t fp ds ss e) -> do
      mem <- funCheckT fp ds ss
      expectedExpType t e >> modify (\_ -> mem)

declsCheckT :: Bool -> [Decl] -> [Ident] -> MemState ()
declsCheckT _ [] fs = checkAllFunT fs >> return ()
declsCheckT b (d:ds) fs = declCheckT b d fs >>= declsCheckT b ds

declCheckT :: Bool -> Decl -> [Ident] -> MemState [Ident]
declCheckT b (DeclD t m@(id:ids)) fs = do
  declVars b t m
  return fs
declCheckT b (DeclWithV t i e) fs = do
  declVar b t i
  expTypeIsGood t e >> return fs
declCheckT True (DeclFun (Func TVoid i fp (FuncBody ds ss))) fs = do
  lookForFun True i Nothing fp ds ss
  return (i:fs)
declCheckT False (DeclFun (Func TVoid i fp (FuncBody ds ss))) fs = do
  lookForFun False i Nothing fp ds ss
  return (i:fs)
declCheckT True (DeclFun (FuncT t i fp (FuncBodyWithR ds ss e))) fs = do
  lookForFun True i (Just (t, e)) fp ds ss
  return (i:fs)
declCheckT False (DeclFun (FuncT t i fp (FuncBodyWithR ds ss e))) fs = do
  lookForFun False i (Just (t, e)) fp ds ss
  return (i:fs)

expectedExpType :: Typ -> Exp -> MemState ()
expectedExpType t e = expTypeIsGood t e

funCheckT :: [FunPar] -> [Decl] -> [Stmt] -> MemState (Mem)
funCheckT fp ds ss = do
  memst@(m1, m2, m1', m2', p) <- MemS.get
  funCheckHelp fp ds ss memst

funCheckHelp :: [FunPar] -> [Decl] -> [Stmt] -> Mem -> MemState (Mem)
funCheckHelp fp ds ss memst@(_, _, m1', m2', _) = do
  ds' <- modify (\(m1,m2,m1',m2',p) -> (m1, m2, Map.empty, Map.empty,p)) >> makeDeclsFromParams fp
  declsCheckT False ds' [] >> declsCheckT False ds [] >> refreshMem m1' m2' >> stmtsCheckT ss >> return memst


makeDeclsFromParams :: [FunPar] -> MemState [Decl]
makeDeclsFromParams [] = return []
makeDeclsFromParams (p@(FunParam t id):ps) = do
  dd <- makeDeclsFromParams ps
  return ((DeclD t [id]):dd)
makeDeclsFromParams (p@(FunParamR t id):ps) = do
  dd <- makeDeclsFromParams ps
  return ((DeclD (funParamType p) [id]):dd)

-- Stmt

stmtsCheckT :: [Stmt] -> MemState ()
stmtsCheckT [] = return ()
stmtsCheckT (s:ss) = stmtCheckT s >> stmtsCheckT ss

stmtCheckT :: Stmt -> MemState ()
stmtCheckT s@(SAss id e) = do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Nothing -> do
      case (lookup id m1) of
        Nothing -> throwError $ "No variable of name " ++ show id ++ " has been declared in " ++ ((render . prt 0) s)
        Just v -> do
          r <- expCheckT (varTypeT v) e
          if r then return ()
          else throwError $ "Cannot assign expesion " ++((render . prt 0) e) ++ "to variable " ++ show id ++ "of type " ++ printType (varTypeT v) ++ " in " ++ ((render . prt 0) s)
    Just v -> do
      r <- expCheckT (varTypeT v) e
      if r then return ()
      else throwError $ "Cannot assign expesion " ++((render . prt 0) e) ++ "to variable " ++ show id ++ "of type " ++ printType (varTypeT v) ++ " in " ++ ((render . prt 0) s)


stmtCheckT s@(SListAss id e1 e2) = do
  t <- expCheckT TInt e1
  if t then do
    (m1, _, m1', _, _) <- MemS.get
    case (lookup id m1') of
      Just (VLB l) -> expTypeIsGood TBool e2
      Just (VLI l) -> expTypeIsGood TInt e2
      Just (VLS l) -> expTypeIsGood TStr e2
      Nothing -> do
        case (lookup id m1) of
          Just (VLB l) -> expTypeIsGood TBool e2
          Just (VLI l) -> expTypeIsGood TInt e2
          Just (VLS l) -> expTypeIsGood TStr e2
          Nothing -> throwError $ "No list of name " ++ show id ++ " has been declared"
          _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope"
      _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope"
  else throwError $ "Index of list must be of type int but get " ++ ((render . prt 0) e1)

stmtCheckT s@(SListDelete id e) = do
  t <- expCheckT TInt e
  if t then do
    (m1, _, m1', _, _) <- MemS.get
    case (lookup id m1') of
      Just (VLB l) -> return ()
      Just (VLI l) -> return ()
      Just (VLS l) -> return ()
      Nothing -> do
        case (lookup id m1) of
          Just (VLB l) -> return ()
          Just (VLI l) -> return ()
          Just (VLS l) -> return ()
          Nothing -> throwError $ "No list of name " ++ show id ++ " has been declared"
          _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope"
      _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope"
  else throwError $ "Index of list must be of type int but get " ++ ((render . prt 0) e)

stmtCheckT (SListClear id) = do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB l) -> return ()
    Just (VLI l) -> return ()
    Just (VLS l) -> return ()
    Nothing -> do
      case (lookup id m1) of
        Just (VLB l) -> return ()
        Just (VLI l) -> return ()
        Just (VLS l) -> return ()
        Nothing -> throwError $ "No list of name " ++ show id ++ " has been declared"
        _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope"
    _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope"


stmtCheckT s@(SListNew id e) = do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB l) -> expTypeIsGood TBool e
    Just (VLI l) -> expTypeIsGood TInt e
    Just (VLS l) -> expTypeIsGood TStr e
    Nothing -> do
      case (lookup id m1) of
        Just (VLB l) -> expTypeIsGood TBool e
        Just (VLI l) -> expTypeIsGood TInt e
        Just (VLS l) -> expTypeIsGood TStr e
        Nothing -> throwError $ "No list of name " ++ show id ++ " has been declared"
        _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope"
    _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope"


stmtCheckT s@(SPrint e) = do
  t <- expCheckT TBool e
  if t then return ()
  else do
    t <- expCheckT TInt e
    if t then return ()
    else do
      t <- expCheckT TStr e
      if t then return ()
      else do
      t <- expCheckT TListBool e
      if t then return ()
      else do
        t <- expCheckT TListInt e
        if t then return ()
        else do
          t <- expCheckT TListStr e
          if t then return ()
          else throwError $ "Unknown type of expresion " ++ ((render . prt 0) e) ++  "in " ++ ((render . prt 0) s)

stmtCheckT s@(SIfS e ss) = do
  t <- expCheckT TBool e
  if t then stmtsCheckT ss
  else throwError $ "Condition " ++ ((render . prt 0) e) ++ "must be bool type in " ++ ((render . prt 0) s)

stmtCheckT s@(SIfElS e1 s1 e2 s2) = do
  t <- expCheckT TBool e1
  if t then do
    t2 <- expCheckT TBool e1
    if t2 then stmtsCheckT s1 >> stmtsCheckT s2
    else throwError $ "Condition " ++ ((render . prt 0) e2) ++ "must be bool type in " ++ ((render . prt 0) s)
  else throwError $ "Condition " ++ ((render . prt 0) e1) ++ "must be bool type in " ++ ((render . prt 0) s)

stmtCheckT s@(SIfElL e1 s1 e2 s2 s3) = do
  t <- expCheckT TBool e1
  if t then do
    t2 <- expCheckT TBool e1
    if t2 then stmtsCheckT s1 >> stmtsCheckT s2 >> stmtsCheckT s3
    else throwError $ "Condition " ++ ((render . prt 0) e2) ++ "must be bool type in " ++ ((render . prt 0) s)
  else throwError $ "Condition " ++ ((render . prt 0) e1) ++ "must be bool type in " ++ ((render . prt 0) s)

stmtCheckT s@(SIfL e s1 s2) = do
  t <- expCheckT TBool e
  if t then stmtsCheckT s1 >> stmtsCheckT s2
  else throwError $ "Condition " ++ ((render . prt 0) e) ++ "must be bool type in " ++ ((render . prt 0) s)

stmtCheckT s@(SWhile e ss) = do
  t <- expCheckT TBool e
  if t then stmtsCheckT ss
  else throwError $ "Condition " ++ ((render . prt 0) e) ++ "must be bool type in " ++ ((render . prt 0) s)


stmtCheckT s@(SCallFunE id) = do
  memst@(_, m2, m1', m2', _) <- MemS.get
  case (lookup id m2') of
    Just (FunctionT _ _ _ _ _) -> throwError $ "Function returns not empty value in " ++ ((render . prt 0) s)
    Just (FunctionV [] ds ss) -> return ()
    Just (FunctionV _ _ _) -> throwError $ "Wrong number of parametrs in " ++ ((render . prt 0) s)
    Nothing -> do
      case (lookup id m2) of
        Just (FunctionT _ _ _ _ _) -> throwError $ "Function returns not empty value in " ++ ((render . prt 0) s)
        Just (FunctionV [] ds ss) -> return ()
        Just (FunctionV _ _ _) -> throwError $ "Wrong number of parametrs in " ++ ((render . prt 0) s)
        Nothing -> throwError $ "No function of name " ++ show id ++ " has been declared in " ++ ((render . prt 0) s)

stmtCheckT s@(SCallFun id exps) = do
  memst@(_, m2, m1', m2', _) <- MemS.get
  case (lookup id m2') of
    Just (FunctionV fp ds ss) ->  matchFunParam fp exps
    Just (FunctionT _ _ _ _ _) -> throwError $ "Function returns not empty value in " ++ ((render . prt 0) s)
    Nothing -> do
      case (lookup id m2) of
        Just (FunctionV fp ds ss) -> matchFunParam fp exps
        Just (FunctionT _ _ _ _ _) -> throwError $ "Function returns not empty value in " ++ ((render . prt 0) s)
        Nothing -> throwError $ "No function of name " ++ show id ++ " has been declared in " ++ ((render . prt 0) s)


-- Exp
expSameType :: Exp -> Exp -> MemState Bool
expSameType e1 e2 = do
  t <- expCheckT TBool e1
  if t then expCheckT TBool e2
  else do
    t <- expCheckT TInt e1
    if t then expCheckT TInt e2
    else do
      t <- expCheckT TStr e1
      if t then expCheckT TStr e2
      else throwError $ "Unknown type of expresion " ++ ((render . prt 0) e1)

expCheckT :: Typ -> Exp -> MemState Bool
expCheckT TBool (EOpA e1 op e2) = do
  first <- expCheckT TBool e1
  if first then do
    second <- expCheckT TBool e2
    return second
  else return first
expCheckT _ (EOpA _ _ _) = return False

expCheckT TBool e@(EOpB e1 op e2) = do
  case op of
    OEq -> do
      r <- expSameType e1 e2
      if r then return True
      else throwError $ "Expresions of different types cannot be compared: " ++ ((render . prt 0) e1) ++ " and "++ ((render . prt 0) e2)
    OEnq -> do
      r <- expSameType e1 e2
      if r then return True
      else throwError $ "Expresions of different types cannot be compared: " ++ ((render . prt 0) e1) ++ " and "++ ((render . prt 0) e2)
    _ -> do
      r <- expCheckT TInt e1
      if r then do
        r <- expCheckT TInt e2
        if r then return True
        else throwError $ "Expected integer value but get " ++ ((render . prt 0) e2) ++ " in " ++ ((render . prt 0) e)
      else throwError $ "Expected integer value but get " ++ ((render . prt 0) e2) ++ " in " ++ ((render . prt 0) e)
expCheckT _ (EOpB _ _ _) = return False

expCheckT TInt (EOpC e1 op e2) = do
  first <- expCheckT TInt e1
  if first then do
    second <- expCheckT TInt e2
    return second
  else return first
expCheckT _ (EOpC _ _ _) = return False

expCheckT TInt (EOpD e1 op e2) = do
  first <- expCheckT TInt e1
  if first then do
    second <- expCheckT TInt e2
    return second
  else return first
expCheckT _ (EOpD _ _ _) = return False

expCheckT t e@(EVar id) =  do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just v -> return (varTypeMatch' v t)
    Nothing -> do
      case (lookup id m1) of
        Just v -> return (varTypeMatch' v t)
        Nothing -> throwError $ "Variable " ++ show id ++ " is undeclared in " ++ ((render . prt 0) e)

expCheckT t e@(EListVar id ee) = do
  ind <- expCheckT TInt ee
  if ind then do
    (m1, _, m1', _, _) <- MemS.get
    case (lookup id m1') of
      Just (VLB _) -> return (t == TBool)
      Just (VLI _) -> return (t == TInt)
      Just (VLS _) -> return (t == TStr)
      Nothing -> do
        case (lookup id m1) of
          Just (VLB _) -> return (t == TBool)
          Just (VLI _) -> return (t == TInt)
          Just (VLS _) -> return (t == TStr)
          _ -> throwError $ "No list with name " ++ show id ++ " has been declared in " ++ ((render . prt 0) e)
      _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope in " ++ ((render . prt 0) e)
  else return False

expCheckT t e@(EListSize id) = do
  (m1, _, m1', _, _) <- MemS.get
  case (lookup id m1') of
    Just (VLB l) -> return True
    Just (VLI l) -> return True
    Just (VLS l) -> return True
    Nothing -> do
      case (lookup id m1) of
        Just (VLB l) -> return True
        Just (VLI l) -> return True
        Just (VLS l) -> return True
        _ -> throwError $ "No list with name " ++ show id ++ " has been declared in " ++ ((render . prt 0) e)
    _ -> throwError $ "Variable " ++ show id ++ " is not a list in that scope in " ++ ((render . prt 0) e)


expCheckT t (EInt _) = return (t == TInt)
expCheckT t (EIntM i) = return (t == TInt)
expCheckT t (EString s) = return (t == TStr)
expCheckT t (EBool _) = return (t == TBool)

expCheckT TListBool (EListEmpty) = return True
expCheckT TListInt (EListEmpty) = return True
expCheckT TListStr (EListEmpty) = return True
expCheckT _ (EListEmpty) = return False

expCheckT TListBool (EListOfV []) = return True
expCheckT TListBool ee@(EListOfV (e:es)) = do
  checkT <- expCheckT TBool e
  if checkT then expCheckT TListBool (EListOfV es)
  else throwError $ "Expresion " ++ ((render . prt 0) e) ++ " expected to be of type bool in " ++ ((render . prt 0) ee)
expCheckT TListStr (EListOfV []) = return True
expCheckT TListStr ee@(EListOfV (e:es)) = do
  checkT <- expCheckT TStr e
  if checkT then expCheckT TListStr (EListOfV es)
  else throwError $ "Expresion " ++ ((render . prt 0) e) ++ " expected to be of type string in " ++ ((render . prt 0) ee)
expCheckT TListInt (EListOfV []) = return True
expCheckT TListInt ee@(EListOfV (e:es)) = do
  checkT <- expCheckT TInt e
  if checkT then expCheckT TListInt (EListOfV es)
  else throwError $ "Expresion " ++ ((render . prt 0) e) ++ " expected to be of type int in " ++ ((render . prt 0) ee)
expCheckT t e@(EListOfV _) = throwError $ "Type " ++ printType t ++ "expected but get list in " ++ ((render . prt 0) e)

expCheckT t e@(EFunE id) = do
  memst@(_, m2, m1', m2', _) <- MemS.get
  case (lookup id m2') of
    Just (FunctionV _ _ _) -> throwError $ "Function returns empty value in " ++ ((render . prt 0) e) ++ " but " ++ printType t ++ " was expected"
    Just (FunctionT t' [] _ _ _) -> return (t == t')
    Just (FunctionT _ _ _ _ _) -> throwError $ "Wrong number of parametrs in " ++ ((render . prt 0) e)
    Nothing -> do
      case (lookup id m2) of
        Just (FunctionV _ _ _) -> throwError $ "Function returns empty value in " ++ ((render . prt 0) e) ++ " but " ++ printType t ++ " was expected"
        Just (FunctionT t' [] ds ss ee) -> return (t == t')
        Just (FunctionT _ _ _ _ _) -> throwError $ "Wrong number of parametrs in " ++ ((render . prt 0) e)
        Nothing -> throwError $ "No function of name " ++ show id ++ " has been declared in " ++ ((render . prt 0) e)


expCheckT t e@(EFun id exps) = do
  memst@(_, m2, m1', m2', _) <- MemS.get
  case (lookup id m2') of
    Just (FunctionT t' fp ds ss ee) -> matchFunParam fp exps >> return (t == t')
    Just (FunctionV _ _ _) -> throwError $ "Function returns empty value in " ++ ((render . prt 0) e) ++ " but " ++ printType t ++ " was expected"
    Nothing -> do
      case (lookup id m2) of
        Just (FunctionT t' fp ds ss ee) -> matchFunParam fp exps >> return (t == t')
        Just (FunctionV _ _ _) -> throwError $ "Function returns empty value in " ++ ((render . prt 0) e) ++ " but " ++ printType t ++ " was expected"
        Nothing -> throwError $ "No function of name " ++ show id ++ " has been declared in " ++ ((render . prt 0) e)




-- sprawdza zgodność prekazanych do funkcji parametrów z oczekiwanymi typami
-- pierwszy parametr to lista, w której znajdują się wszystkie zmienne, nazwy których w funkcji były na liście
-- parametrów, oraz (Nothing, id) oznacza że parametr był przekaany przez wartość, a (Just id, id') - przez zmienna,
-- gdzie id to nazwa tej zmiennej w poprzednim środowisku lokalnym lub globalnym
matchFunParam :: [FunPar] -> [Exp] -> MemState ()
matchFunParam [] [] = return ()
matchFunParam [] (e:es) = throwError $ "Too much parameters in function "
matchFunParam (p:ps) [] = throwError $ "Too few parameters in function "
matchFunParam (p@(FunParam t _):ps) (e:es) = do
  r <- expCheckT t e
  if r then matchFunParam ps es
  else throwError $ "Parameter of type " ++ printType t ++ " expected in " ++ ((render . prt 0) e) ++ " in function parameter " ++ ((render . prt 0) p)
matchFunParam (p@(FunParamR _ _):ps) (e:es) = do
  case e of
    (EVar id) -> do
      r <- expCheckT (funParamType p) e
      if r then matchFunParam ps es
      else throwError $ "Parameter of type " ++ printType (funParamType p) ++ " expected in " ++ ((render . prt 0) e) ++ " in function parameter " ++ ((render . prt 0) p)
    _ -> throwError $ "Variable name expected but get " ++ ((render . prt 0) e) ++ " in function parameter " ++ ((render . prt 0) p)

-- sprawdzamy czy typ funkcji jest zgodny z wynikiem
checkExpT :: Typ -> Exp -> [(Maybe Ident, Ident)] -> MemState ([(Maybe Ident, Ident)], Var)
checkExpT t e re = do
  v <- evalExp e
  if varTypeMatch' v t then return (re, v)
  else throwError $ "Return type " ++ varType v ++
       " doesn't match function type " ++ show t


