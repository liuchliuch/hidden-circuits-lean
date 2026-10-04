import HiddenCircuits.Complexity.GridWeightsRuntime
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioNormalization
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCombine
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryAlgebra

/-! Fresh reconstruction of the physical ratio-cell layout. Masters 0–6 are
preserved, outputs 7–8 are signed integers, and all scratch ports are erased. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

def fields (dt nt ds ns norm sign answer : BitString) : Store 52 := fun i =>
  if i.val=9 then dt else if i.val=10 then nt else if i.val=11 then ds else if i.val=12 then ns
  else if i.val=13 then norm else if i.val=14 then sign else if i.val=15 then answer else []
def state (t k s l p h : ℕ) (answer num den : BitString) (work : Store 52) : Store 52 := fun i =>
  if i.val=0 then List.replicate t true else if i.val=1 then List.replicate k true
  else if i.val=2 then List.replicate s true else if i.val=3 then List.replicate l true
  else if i.val=4 then List.replicate p true else if i.val=5 then List.replicate h true
  else if i.val=6 then answer else if i.val=7 then num else if i.val=8 then den else work i

def leftEmbedding : Fin 16 ↪ Fin 53 where
  toFun i := ![0,1,9,10,16,17,18,19,20,21,22,23,24,25,26,27] i
  inj' := by decide +kernel
def rightEmbedding : Fin 16 ↪ Fin 53 where
  toFun i := ![2,3,11,12,16,17,18,19,20,21,22,23,24,25,26,27] i
  inj' := by decide +kernel
def normEmbedding : Fin 22 ↪ Fin 53 where
  toFun i := ![2,5,4,13,14,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32] i
  inj' := by decide +kernel
def combineEmbedding : Fin 16 ↪ Fin 53 where
  toFun i := ![7,8,16,17,18,19,20,21,22,14,15,10,12,9,11,13] i
  inj' := by decide +kernel
noncomputable def left : OracleBlock 52 := rename GridWeightsRuntime.pairProgram leftEmbedding
noncomputable def right : OracleBlock 52 := rename GridWeightsRuntime.pairProgram rightEmbedding
noncomputable def norm : OracleBlock 52 := rename RatioNormalization.program normEmbedding
noncomputable def copyAnswer : OracleBlock 52 := copyOn 6 15 16 (by decide) (by decide) (by decide)
noncomputable def combine : OracleBlock 52 := rename RatioCombine.program combineEmbedding
noncomputable def program : OracleBlock 52 := seq left (seq right (seq norm (seq copyAnswer combine)))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
