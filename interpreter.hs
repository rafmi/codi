module Main where

import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Data.Maybe
import qualified Data.Map as Map

import LexCodi
import ParCodi
import SkelCodi
import PrintCodi
import AbsCodi

import System.IO
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )
import ErrM


type Name = Ident
type Size = Integer
type Type = CType

data Value = IntVal Integer
           | StrVal String
           | FunVal Type [Ident] Block
           | BooleanVal Bool
           | NoVal
  deriving(Show)

data ProgState = BREAK
               | RETURN Value
               | NORMAL
               | CONTINUE

data DeclareType = BasicType Type | FunType Type [Type]
  deriving(Show)

type Memory = Map.Map Integer Value
type VarInfos = Map.Map Name (DeclareType, Integer)
type Environment = (VarInfos, Size)
type Eval ev = StateT Memory (ReaderT Environment (ExceptT String IO)) ev

showI :: Ident -> String
showI (Ident s) = s

runEval :: Memory -> Environment -> Eval alfa -> IO (Either String (alfa, Memory))
runEval mem env ev = runExceptT (runReaderT (runStateT ev mem) env)

declareVar :: Environment -> TypeDecl -> Eval Environment
declareVar (varInfos, varsCount) (DeclVar t name) = do
    mem <- get
    put $ Map.insert varsCount NoVal mem
    let    
      newVarInfos = Map.insert name (BasicType t, varsCount) varInfos in
      return $ (newVarInfos, varsCount+1)

declareVar (varInfos, varsCount) (DeclFun ret name args) = do
    mem <- get
    put $ Map.insert varsCount NoVal mem
    let    
      getType :: DeclArg -> CType
      getType (EDeclArg t n) = t
      newVarInfos = Map.insert name (FunType ret (fmap getType args), varsCount) varInfos in
      return $ (newVarInfos, varsCount+1)

declareVars :: Environment -> Vars -> Eval Environment
declareVars vs VarsEmpty = return $ vs
declareVars vs (EVars decs) = declare vs decs where
    declare :: Environment -> [TypeDecl] -> Eval Environment
    declare = foldM declareVar

liftInt :: (Integer -> Integer -> Integer) -> (Value -> Value -> Value)
liftInt f = f2 where
    f2 (IntVal x) (IntVal y) = IntVal (f x y)

liftCompare :: (Integer -> Integer -> Bool) -> (Value -> Value -> Value)
liftCompare f = f2 where
    f2 (IntVal x) (IntVal y) = BooleanVal (f x y)
liftLogical :: (Bool -> Bool -> Bool) -> (Value -> Value -> Value)
liftLogical f = f2 where
    f2 (BooleanVal x) (BooleanVal y) = BooleanVal (f x y)

evalBinaryOp :: Exp -> Exp -> (Value -> Value -> Value) -> Type -> Eval Value
evalBinaryOp e1 e2 f t = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType t ev1
    checkType t ev2
    return $ f ev1 ev2

eval :: Exp -> Eval Value
eval (EOr e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Bool ev1
    checkType Bool ev2
    return $ liftLogical (||) ev1 ev2

eval (EAnd e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Bool ev1
    checkType Bool ev2
    return $ liftLogical (&&) ev1 ev2

eval (EEqual e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkSameTypes ev1 ev2
    checkTypes [Int, Bool, Str] ev1
    checkTypes [Int, Bool, Str] ev2
    return $ (equal) ev1 ev2 where
      equal :: Value -> Value -> Value
      equal (IntVal i) (IntVal j) = BooleanVal (i == j)
      equal (StrVal i) (StrVal j) = BooleanVal (i == j)
      equal (BooleanVal i) (BooleanVal j) = BooleanVal (i == j)
      equal _ _ = BooleanVal False

eval (ENequal e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkSameTypes ev1 ev2
    checkTypes [Int, Bool, Str] ev1
    checkTypes [Int, Bool, Str] ev2
    return $ (nequal) ev1 ev2 where
      nequal :: Value -> Value -> Value
      nequal (IntVal i) (IntVal j) = BooleanVal (i /= j)
      nequal (StrVal i) (StrVal j) = BooleanVal (i /= j)
      nequal (BooleanVal i) (BooleanVal j) = BooleanVal (i /= j)
      nequal _ _ = BooleanVal True

eval (ELess e1 e2) = evalBinaryOp e1 e2 (liftCompare (<)) Int

eval (ELeq e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Int ev1
    checkType Int ev2
    return $ (liftCompare (<=)) ev1 ev2

eval (EMore e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Int ev1
    checkType Int ev2
    return $ (liftCompare (>)) ev1 ev2

eval (EMeq e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Int ev1
    checkType Int ev2
    return $ (liftCompare (>=)) ev1 ev2

eval (EPlus e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Int ev1
    checkType Int ev2
    return $ (liftInt (+)) ev1 ev2

eval (EMinus e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Int ev1
    checkType Int ev2
    return $ (liftInt (-)) ev1 ev2

eval (ETimes e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Int ev1
    checkType Int ev2
    return $ (liftInt (*)) ev1 ev2

eval (EDiv e1 e2) = do
    ev1 <- eval e1
    ev2 <- eval e2
    checkType Int ev1
    checkType Int ev2
    case ev2 of
      IntVal 0 -> throwError "dividing by 0 error"
      _ -> return $ (liftInt (div)) ev1 ev2

eval (ECall name args) = do
    mem <- get
    (varInfo, memsize) <- ask
    case Map.lookup name varInfo of
      Just (FunType retType argTypes, pos) -> case Map.lookup pos mem of
        Just (FunVal retType argNames block) ->  do
          newVars <- declareFunArgs (varInfo, memsize) argNames argTypes args
          pState <- local (const newVars) (runBlock block)
          case pState of
            RETURN x -> do
              checkType retType x
              return $ x
            NORMAL -> do
              checkType retType NoVal
              return $ NoVal
            _ -> throwError ((showI name) ++ " doesn't return anything")
        _ -> throwError "function undeclared"
      Just _ -> throwError ((showI name) ++ " declared not as a function")
      Nothing -> throwError ((showI name) ++ " function undeclared")

eval (EVar (EVarName name)) = do
    mem <- get
    (vars, _) <- ask
    case Map.lookup name vars of 
      Just (BasicType t, pos) -> case Map.lookup pos mem of
          Just NoVal -> throwError ((showI name) ++ " has no value")
          Just val -> return val
      Just _ -> throwError ((showI name) ++ " cannot be used as right value")
      Nothing -> throwError ((showI name) ++ " undeclared")

eval (EInt i) = return $ IntVal i
eval (EBool (BoolVal "True")) = return $ BooleanVal True
eval (EBool (BoolVal "False")) = return $ BooleanVal False
eval (EStr s) = return $ StrVal s
eval (EPar exp) = do eval exp

checkTypeVal :: (Type, Value) -> Bool
checkTypeVal p = case p of
  (Int, IntVal _) -> True
  (Str, StrVal _) -> True
  (Bool, BooleanVal _) -> True
  (Void, NoVal) -> True
  _ -> False

checkArgs :: [Type] -> [Value] -> Bool
checkArgs types vals = any (not . checkTypeVal) (zip types vals)

checkType :: Type -> Value -> Eval ()
checkType Int (IntVal _) = return ()
checkType Str (StrVal _) = return ()
checkType Bool (BooleanVal _) = return ()
checkType Void NoVal = return ()
checkType t v = throwError ("incorrect types: " ++ (show t) ++ " " ++ (show v))

checkTypes :: [Type] -> Value -> Eval ()
checkTypes types val = case any (ct val) types of
    True -> return ()
    False -> throwError "inconsistent types"
    where
      ct (IntVal _) Int = True
      ct (StrVal _) Str = True
      ct (BooleanVal _) Bool = True
      ct _ _ = False

checkTypesEqual :: Type -> Type -> Eval()
checkTypesEqual Int Int = return ()
checkTypesEqual Str Str = return ()
checkTypesEqual Bool Bool = return ()
checkTypesEqual a b = throwError ("inconsistent types: " ++ (show a) ++ (show b))

checkSameTypes :: Value -> Value -> Eval ()
checkSameTypes (IntVal _) (IntVal _) = return ()
checkSameTypes (StrVal _) (StrVal _) = return ()
checkSameTypes (BooleanVal _) (BooleanVal _) = return ()
checkSameTypes NoVal NoVal = return ()
checkSameTypes (FunVal _ _ _) (FunVal _ _ _) = return ()
checkSameTypes a b = throwError ("inconsistent types: " ++ (show a) ++ (show b))

declareFunArg :: Environment -> Ident -> Type -> FunArg -> Eval Environment
declareFunArg (varInfos, size) varName varType (FunArgCopy e) = do
    ev <- eval e
    mem <- get
    checkType varType ev
    put $ Map.insert size ev mem
    return $ (Map.insert varName (BasicType varType, size) varInfos, size+1)

declareFunArg (varInfos, size) varName varType (FunArgRef (EVarName name)) = do
    mem <- get
    case Map.lookup name varInfos of
      Just (BasicType typ, pos) -> do
        checkTypesEqual typ varType
        return $ (Map.insert varName (BasicType typ, pos) varInfos, size)
      _ -> throwError ((showI name) ++ "undeclared")


declareFunArgs :: Environment -> [Ident] -> [Type] -> [FunArg] -> Eval Environment
declareFunArgs vs [] [] [] = return vs
declareFunArgs vs (vn:varNames) (vt:varTypes) (fa:funArgs) = do
    vs2 <- declareFunArg vs vn vt fa
    declareFunArgs vs2 varNames varTypes funArgs
          
run :: Instr -> Eval ProgState
run (IPass) = return NORMAL
run (IContinue) = return CONTINUE
run (IWhile cond nested) = do
    ev <- eval cond
    case ev of
        BooleanVal condition -> if condition then do
            pState <- runBlock nested
            case pState of
                NORMAL -> run (IWhile cond nested)
                BREAK -> return NORMAL
                CONTINUE -> run (IWhile cond nested)
                RETURN x -> return $ RETURN x
        else return NORMAL
run (IIf exp ni1 [] ni2) = do
    ev <- eval exp
    case ev of
        BooleanVal condition -> if condition then runBlock ni1 else runBlock ni2

run (EAss (EVarName name) e) = do
    ev <- eval e
    mem <- get
    (varPos, memSize) <- ask
    case Map.lookup name varPos of
      Just (t, pos) -> do
        put $ Map.insert pos ev mem
        return $ NORMAL
      _ -> throwError $ (showI name) ++ " uninitalized"

run (IExp e) = do
    ev <- eval e
    return $ NORMAL

run (IPrint exp) = do
    ev <- eval exp
    liftIO $ print ev
    return $ NORMAL

run IBreak = return $ BREAK

run (IReturn e) = do
    ev <- eval e
    return $ RETURN ev


defFun :: FunDef -> Eval ()
defFun (EFunDef name args block) = do
    mem <- get
    (varInfo, memSize) <- ask
    case Map.lookup name varInfo of
      Just (FunType t _, pos) -> put $ Map.insert pos (FunVal t args block) mem
      Nothing -> do
          liftIO (print  name)
          return ()
    return ()
defFuns :: [FunDef] -> Eval()
defFuns [] = return ()
defFuns (h:t) = do
    defFun h
    defFuns t


runAll :: [Instr] -> Eval ProgState
runAll (h:t) = do
    pState <- run h
    case pState of
        NORMAL -> runAll t
        BREAK -> return BREAK
        CONTINUE -> return CONTINUE
        RETURN x -> return $ RETURN x
runAll [] = return NORMAL

runBlock :: Block -> Eval ProgState
runBlock (EBlock vars funDefs instrs) = do
    positions <- ask
    newVars <- declareVars positions vars
    local (const newVars) (defFuns funDefs)
    local (const newVars) (runAll instrs)

runProgram :: Program -> Eval ProgState
runProgram (EProgram [] varDecl funDefs instrL) = do
    positions <- ask
    newVars <- declareVars positions varDecl
    local (const newVars) (defFuns funDefs)
    local (const newVars) (runAll instrL)

--
--Some functions used for preprocessing (Inserting INDENT, DEDENT, NEWLINE tokens
--They are very similar to begin..end

measureIndent :: String -> Int
measureIndent [] = 0
measureIndent (' ':t) = 1 + measureIndent t
measureIndent (_:_) = 0

indentation :: String -> [Int]
indentation = (map measureIndent) . lines

indentsDedents :: String  -> ([Int], [Int])
indentsDedents s = (map (subtract 1) (reverse dedents), reverse indents) where
  (dedents, indents) = findIndents 0 [0] [] [] spaces
  spaces = indentation s

addDedents :: Int -> [Int] -> [Int] -> [Int] -> [Int] -> ([Int], [Int])
addDedents i (st:stack) dedents indents [] = (dedents, indents)
addDedents i (st:stack) dedents indents (sp:spaces) = case st > sp of
  True -> addDedents i stack (i:dedents) indents (sp:spaces)
  False -> findIndents (i+1) (st:stack) dedents indents (spaces)

findIndents :: Int -> [Int] -> [Int] -> [Int] -> [Int] -> ([Int], [Int])
findIndents i (st) (deds) (indents) [] = (deds, indents)
findIndents i (st:stack) deds indents (sp:spaces) = case st < sp of
    True -> addDedents i (sp:st:stack) deds (i:indents) (sp:spaces)
    False -> addDedents i (st:stack) deds indents (sp:spaces)

prependIndents :: Int -> [Int] -> [String] -> [String]
prependIndents i [] ss = ss
prependIndents i (ln:t) (s:ss) = case i == ln of
    True -> prependIndents i t (("INDENT " ++ s):ss)
    False -> case i < ln of
      True -> (s:prependIndents (i+1) (ln:t) (ss))
      False -> prependIndents i t (s:ss)

appendDedents :: Int -> [Int] -> [String] -> [String]
appendDedents i [] ss = ss
appendDedents i (ln:t) (s:ss) = case i == ln of
    True -> appendDedents i t ((s ++ " DEDENT"):ss)
    False -> case i < ln of
      True -> (s:appendDedents (i+1) (ln:t) (ss))
      False -> appendDedents i t (s:ss)


addTokens s = ret where
  str = s ++ "pass\n"
  (dedents, indents) = indentsDedents str
  l1 = lines str
  l2 = prependIndents 0 indents l1
  l3 = appendDedents 0 dedents l2
  l4 = map (++" NEWLINE\n") l3
  ret = concat l4
--
--
--

strToProg = pProgram . myLexer

printErr :: String -> IO ()
printErr s = hPutStrLn stderr s

runInterpreter str = do
  case (strToProg (addTokens str)) of
    Ok tree ->  do
      result <- runEval (Map.empty) (Map.empty, 0) (runProgram tree)
      case result of
        Left errMessage -> printErr errMessage
        _ -> exitSuccess
    Bad s -> do
      printErr "Parse failed..."
      printErr s
      exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> do 
        inp <- hGetContents stdin 
        runInterpreter inp
    [progName] -> do
        inp <- readFile progName
        runInterpreter inp
    _ -> do
      printErr "Wrong number of arguments, usage:"
      printErr "./interpreter < prog.co or ./interpreter prog.co"
      exitFailure
