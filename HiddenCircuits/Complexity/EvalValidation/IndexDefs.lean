import HiddenCircuits.Complexity.GraphVerifier.HeaderStage
import HiddenCircuits.Complexity.GraphVerifier.LengthAtLeast
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! A real all-input validator for unary indices below a width minus one. -/
namespace HiddenCircuits.Complexity.EvalValidation.Index
open OracleBlock GraphVerifier GraphVerifier.Runtime
set_option maxHeartbeats 800000

def valid (xs width : BitString) : Bool := xs.all id && decide (xs.length+2≤width.length)
def store (xs width out len all copy bound : BitString) : Store 8 :=
  ![xs,width,out,len,[],all,copy,bound,[]]
def headerPorts : Fin 4 ↪ Fin 9 where
  toFun i:=![0,3,4,5] i
  inj' := by decide +kernel
def comparePorts : Fin 3 ↪ Fin 9 where
  toFun i:=![6,3,7] i
  inj' := by decide +kernel
noncomputable def before : OracleBlock 8 := seq (headerOn headerPorts)
  (seq (prepend 3 [true,true]) (copyOn 1 6 8 (by decide) (by decide) (by decide)))
noncomputable def after : OracleBlock 8 := seq (clearList [0,3,6])
  (decision 2 [5,7] (fun bs=>bs.all id))
noncomputable def program : OracleBlock 8 := seq before (seq (rename lengthAtLeastBlock comparePorts) after)

end HiddenCircuits.Complexity.EvalValidation.Index
