module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Debug.Trace
import Text.Show.Functions ()

type VEnv = E.Env Value

data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           -- Add other variants as needed
           deriving (Show, Read)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)

data VirStack = Arg1 Exp
              | Arg2 Exp 
              deriving(Show,Read)

type Stack = [VirStack]

data CurrState = CurrentstateExp Exp 
              | CurrentstateVal Value
              deriving(Show,Read)

data MachineState = MEval Stack VEnv CurrState 
                  | Mcal Stack VEnv CurrState
                  deriving(Show,Read)



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
msInitialState state = Mcal [] E.empty ( CurrentstateExp state )

-- checks whether machine is in final state
msInFinalState :: MachineState -> Bool
msInFinalState (Mcal stack vEnv currentExpr) = case stack of
  [] -> case currentExpr of
    CurrentstateExp expr -> case expr of
      Con str -> case str of
        "True" -> True 
        "False" -> True 
        "Nil" -> True 
    CurrentstateVal value -> case value of 
      B True -> True 
      B False -> False 
      Nil -> True 
      I n -> True 
      Cons n e -> True 
  _ ->False


-- returns the final value if machine is in final state. If the machine is not in final state, throw an error
msGetValue :: MachineState -> Value
msGetValue (MEval _ _ currentExpr) = case currentExpr of
  CurrentstateVal value -> case value of
                     B True -> B True
                     B False -> B False
                     Nil ->  Nil
                     I n -> I n
                     (Cons n e) -> Cons n e
  
msStep :: MachineState -> MachineState
msStep (Mcal stack vEnv currentExpr) = case currentExpr of
  CurrentstateExp ( Con str) -> case str of
                      "True" -> MEval stack vEnv (CurrentstateVal(B True))
                      "False"-> MEval stack vEnv (CurrentstateVal(B False))
                      "Nil" -> MEval stack vEnv (CurrentstateVal Nil)
  CurrentstateExp (Num n) -> MEval stack vEnv (CurrentstateVal(B True))

   --List operations
  CurrentstateExp(App (Prim Head) e2) -> case e2 of
    Con "Nil" -> error "list is empty"
    App (App (Con "Cons") (Num n)) e2 -> MEval stack vEnv currentExpr 
                                           where
                                             currentExpr = CurrentStateVal (I n)
  CurrentstateExp(App (Prim Tail) e2) -> case e2 of
    Con "Nil" -> error "list is empty"
    App (App (Con "Cons") (Num n)) e2 -> case e2 of
          Con "Nil" -> MSevaluate stack vEnv currentExpr
                        where
                          currentExp = CurrentStateVal (Cons n Nil)
  
  CurrentstateExp(App (Prim Null) e2) -> case e2 of
    Con "Nil" ->  MSevaluate stack vEnv (CurrentStateVal (B True))
    _ ->  MSevaluate stack vEnv (CurrentStateVal (B False))
