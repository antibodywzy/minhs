module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Debug.Trace
import Text.Show.Functions ()
import MinHS.Parse (expr)
data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           | Expr Exp
           | Closure Environment Exp
           deriving (Show,Eq)

data VCurrentState = CurrentStateExp Exp
                   | CurrentStateVal Value
                   deriving(Show,Eq)

data VStack = BinOpArg1 Exp
            | BinOpArg2 Exp
            | BinOpArg3 Exp Exp
            | AppFunc Exp
            | AppFuncArg Exp
            | EnvStack Environment 
            | AppClosure Environment Exp         
            deriving(Show,Eq)

type Stack = [VStack]

type VEnv = E.Env Value
type BindEnv = E.Env Bind

type Environment = (VEnv,BindEnv)

data MachineState = MSevaluate Stack Environment VCurrentState
                  | MScalculate Stack Environment VCurrentState 
                  deriving(Show,Eq)


--Auxillary Functions
frameToExp :: VStack -> Exp
frameToExp frame  = case frame of
  BinOpArg1 expr -> expr
  BinOpArg2 expr -> expr
  AppFunc expr -> expr
stateToExp :: VCurrentState -> Exp
stateToExp state = case state of
  CurrentStateExp (expr) -> expr
  CurrentStateVal (value) -> case value of
    I n -> Num n
    B True -> Con "True"
    B False -> Con "False"

stateToVal :: VCurrentState -> Value
stateToVal state = case state of
  CurrentStateVal (value) -> case value of
    I n -> I n
    B True -> B True  
    B False -> B False

frameToFunc :: VStack -> Id
frameToFunc (AppFunc(Recfun(Bind var1 typ var2 body))) = var1 

frameToBind :: VStack -> Bind
frameToBind (AppFunc(Recfun(Bind var1 typ var2 body))) = (Bind var1 typ var2 body)

frameToBinding :: VStack -> Id
frameToBinding (AppFunc(Recfun(Bind var1 typ var2 body))) = case var2 of
  [binding] -> binding

frameToId :: [Id] -> Id
frameToId [v] = v

frameToBody :: VStack -> Exp
frameToBody (AppFunc(Recfun(Bind var1 typ var2 body))) = body

maybeToval :: Maybe Value -> Exp
maybeToval v = case v of
  Just val -> case val of
    I n -> Num n
    B True -> Con "True"
    B False -> Con "False"
  Nothing -> error "Variable not in environment"

maybeToExp :: Maybe Bind -> Exp
maybeToExp v = case v of
  Just (Bind var1 typ var2 body) -> body
  Nothing -> error "Variable not in environment"

stackEnvToEnv :: VStack -> Environment
stackEnvToEnv (EnvStack (v,e)) = (v,e)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)


-- do not change this definition
evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE e
evaluate _ = error "Input program did not have exactly one binding"

-- do not change this definition
evalE :: Exp -> Value
evalE expr = loop (msInitialState expr)
  where 
    loop ms =  (trace (show expr)) $  -- uncomment this line and pretty print the machine state/parts of it to
                                            -- observe the machine states
             if (msInFinalState newMsState)
                then msGetValue newMsState
                else loop newMsState
              where
                 newMsState = msStep ms


msInitialState :: Exp -> MachineState
msInitialState state = MScalculate [] (E.empty, E.empty) (CurrentStateExp state) 


-- checks whether machine is in final state
msInFinalState :: MachineState -> Bool
msInFinalState (MSevaluate stack (vEnv,bindEnv) currentExpr) = case stack of
  [] -> case currentExpr of
      CurrentStateVal value -> case value of
                              B True -> True
                              B False -> True
                              Nil -> True
                              I n -> True
                              Cons n e -> True
      CurrentStateExp expr -> case expr of
               Con str -> case str of
                "True" -> True
                "False" -> True
                "Nil" -> True
  _ -> False


-- returns the final value, if machine in final state, Nothing otherwise
msGetValue :: MachineState -> Value
msGetValue (MSevaluate _ _ currentExpr) = case currentExpr of
  CurrentStateVal value -> case value of
                     B True -> B True
                     B False -> B False
                     Nil ->  Nil
                     I n -> I n
                     (Cons n e) -> Cons n e


--Calculation mode
msStep :: MachineState -> MachineState
msStep (MScalculate stack (vEnv,bindEnv) currentExpr ) = do
  case currentExpr of

    --Basic values
    CurrentStateExp (Con str) ->  case str of
                      "True" -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B True))
                      "False" -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B False)) 
                      "Nil" ->  MSevaluate stack (vEnv,bindEnv) (CurrentStateVal Nil)

    CurrentStateExp (Num n) ->  MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I n))

    
    --List operations
    CurrentStateExp(App (Prim Head) e2) -> case e2 of
      Con "Nil" -> error "list is empty"
      App (App (Con "Cons") (Num n)) e2 -> MSevaluate stack (vEnv,bindEnv) currentExpr
                                            where
                                              currentExpr = CurrentStateVal (I n)
    CurrentStateExp(App (Prim Tail) e2) -> case e2 of
        Con "Nil" -> error "list is empty"
        App (App (Con "Cons") (Num n)) e2 -> case e2 of
          Con "Nil" -> MSevaluate stack (vEnv,bindEnv) currentExpr 
                        where
                          currentExpr = CurrentStateVal (Cons n Nil)
  
    CurrentStateExp(App (Prim Null) e2) -> case e2 of
      Con "Nil" ->  MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B True))
      _ ->  MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B False)) 
      
    --Binary operations
    CurrentStateExp (App (App (Prim op) (Num num1)) (Num num2))  ->  case op of
      Add -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (num1 + num2))) 
      Sub -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (num1 - num2)))
      Mul -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (num1 * num2)))
      Quot -> if num2 == 0
            then error "Division by zero"
            else MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (quot num1 num2)))
      Gt -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 > num2))) 
      Ge -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 >= num2))) 
      Lt -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 < num2))) 
      Le -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 <= num2))) 
      Eq -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 == num2))) 
      Ne -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (B (num1 /= num2))) 

    CurrentStateExp (App(Prim Neg) (Num num1)) -> MSevaluate stack (vEnv,bindEnv) (CurrentStateVal (I (negate num1)))
    CurrentStateExp (App (Prim op) (Num num1)) ->  MScalculate (update:frames) (vEnv,bindEnv) currentExpr 
                                                      where
                                                        pop = head stack
                                                        arg2 = frameToExp pop
                                                        update = BinOpArg1 (App (Prim op) (Num num1))
                                                        frames = tail stack
                                                        currentExpr = CurrentStateExp (arg2)

    CurrentStateExp (App (Prim op) expr2) -> MScalculate (update:frames) (vEnv,bindEnv) currentExpr
                                              where
                                                update = BinOpArg1 (Prim op)
                                                frames = stack
                                                currentExpr = CurrentStateExp (expr2)

    CurrentStateExp (App(App(Prim op) (Var ch)) (Num n)) -> MScalculate stack (vEnv,bindEnv) currentExpr 
                                                             where
                                                               lookupEnv = E.lookup vEnv ch
                                                               value = maybeToval lookupEnv
                                                               currentExpr = CurrentStateExp (App(App(Prim op) (value)) (Num n))
                                                          
    CurrentStateExp (App expr1 expr2) -> MScalculate (update:frames) (vEnv,bindEnv) currentExpr 
                                          where
                                            update = BinOpArg2 expr2
                                            frames = stack
                                            currentExpr = CurrentStateExp (expr1)
    
    --If then else operation
    CurrentStateExp (If e1 e2 e3) -> case e1 of
      Con str -> case str of
        "True" -> MScalculate stack (vEnv,bindEnv) (CurrentStateExp e2) 
        "False" -> MScalculate stack (vEnv,bindEnv) (CurrentStateExp e3) 
      _ -> MScalculate (update:frames) (vEnv,bindEnv) (CurrentStateExp e1) 
            where
              update = BinOpArg3 e2 e3
              frames = stack
