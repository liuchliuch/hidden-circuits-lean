import HiddenCircuits.Complexity.EvenWeights
import HiddenCircuits.Complexity.GridWeightsRuntime
import HiddenCircuits.GraphReduction.Runtime.WordGraph.OddFactorialRuntime
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioNormalization
import HiddenCircuits.Complexity.BinaryArithmetic.UnaryBinary

/-! Fresh physical setup for generation of both signed even-node weights. -/
namespace HiddenCircuits.Complexity.EvenWeightsRuntime
open OracleBlock BinaryArithmetic Polynomial
open HiddenCircuits.GraphReduction
open HiddenCircuits.GraphReduction.Runtime.WordGraph
set_option maxHeartbeats 900000

def state (i k : ℕ) (den num fact power divisor sign : BitString) : Store 30 := fun q =>
  if q.val=0 then List.replicate i true else if q.val=1 then List.replicate k true
  else if q.val=2 then den else if q.val=3 then num else if q.val=4 then fact
  else if q.val=6 then power else if q.val=7 then divisor else if q.val=8 then sign else []

def ordinaryEmbedding : Fin 16 ↪ Fin 31 where
  toFun i := ![0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20] i
  inj' := by decide +kernel
def oddEmbedding : Fin 17 ↪ Fin 31 where
  toFun i := ![26,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24] i
  inj' := by decide +kernel
def powerEmbedding : Fin 17 ↪ Fin 31 where
  toFun i := ![26,25,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] i
  inj' := by decide +kernel
def unaryEmbedding : Fin 3 ↪ Fin 31 where
  toFun i := ![25,26,29] i
  inj' := by decide +kernel
def parityEmbedding : Fin 2 ↪ Fin 31 where
  toFun i := ![25,8] i
  inj' := by decide +kernel

noncomputable def ordinary : OracleBlock 30 := seq (rename GridWeightsRuntime.pairProgram ordinaryEmbedding) (clear 3)
noncomputable def sumClock : OracleBlock 30 := seq (copyOn 0 25 29 (by decide) (by decide) (by decide))
  (copyOn 1 25 29 (by decide) (by decide) (by decide))
noncomputable def oddClock : OracleBlock 30 := seq (copyOn 0 26 29 (by decide) (by decide) (by decide))
  (seq (copyOn 1 26 29 (by decide) (by decide) (by decide)) (push 26 true))
noncomputable def divisorClock : OracleBlock 30 := seq (copyOn 0 25 29 (by decide) (by decide) (by decide))
  (seq (copyOn 0 25 29 (by decide) (by decide) (by decide)) (push 25 true))
noncomputable def fact : OracleBlock 30 := seq oddClock (seq (rename OddFactorialRuntime.program oddEmbedding)
  (moveOn 26 4 29 (by decide) (by decide) (by decide)))
noncomputable def powerConstants : OracleBlock 30 := seq (push 26 true) (seq (push 26 false) (push 26 false))
noncomputable def power : OracleBlock 30 := seq sumClock (seq powerConstants
  (seq (rename PowerRuntime.program powerEmbedding) (moveOn 26 6 29 (by decide) (by decide) (by decide))))
noncomputable def divisor : OracleBlock 30 := seq divisorClock (seq (rename unaryBinary unaryEmbedding)
  (seq (push 26 false) (moveOn 26 7 29 (by decide) (by decide) (by decide))))
noncomputable def sign : OracleBlock 30 := seq sumClock (seq (push 8 true) (rename parityBlock parityEmbedding))

lemma ordinary_executes (g : BitString → ℕ) (d : ℕ) (i : Fin (d+1)) :
    ∃c, ordinary.Executes g (state i.val (d-i.val) [] [] [] [] [] [])
      (state i.val (d-i.val) (signedBits (interpolationDenominator d i)) [] [] [] [] []) c ∧
      c ≤ GridWeightsRuntime.pairTime.eval d+d^2+5 := by
  obtain ⟨a,ha,hab⟩ := GridWeightsRuntime.pairProgram_executes g d i
  have hrun : (rename GridWeightsRuntime.pairProgram ordinaryEmbedding).Executes g
      (state i.val (d-i.val) [] [] [] [] [] [])
      (state i.val (d-i.val) (signedBits (interpolationDenominator d i)) (signedBits (interpolationNegativeNumerator d i)) [] [] [] []) a := by
    apply rename_executes_to GridWeightsRuntime.pairProgram ordinaryEmbedding g ha
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq
      have h2 : q.val≠2 := by intro h;exact hq 2 (Fin.ext h.symm)
      have h3 : q.val≠3 := by intro h;exact hq 3 (Fin.ext h.symm)
      simp only [state,h2,h3,if_false]
  have hc : (clear (3:Fin 31)).Executes g
      (state i.val (d-i.val) (signedBits (interpolationDenominator d i)) (signedBits (interpolationNegativeNumerator d i)) [] [] [] [])
      (state i.val (d-i.val) (signedBits (interpolationDenominator d i)) [] [] [] [] [])
      ((signedBits (interpolationNegativeNumerator d i)).length+1) := by
    convert clear_executes g (3:Fin 31) (state i.val (d-i.val) (signedBits (interpolationDenominator d i))
      (signedBits (interpolationNegativeNumerator d i)) [] [] [] []) using 1
    funext q;fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g hrun hc,?_⟩
  have hh := (interpolation_weights_bit_bound d i).2
  simp only [signedBits,List.length_cons,encodeNat_length]
  omega

lemma sumClock_executes (g : BitString → ℕ) (i k : ℕ) (den num f p v s : BitString) :
    sumClock.Executes g (state i k den num f p v s)
      (Function.update (state i k den num f p v s) (25:Fin 31) (List.replicate (i+k) true)) (5*i+5*k+6) := by
  let st := state i k den num f p v s
  let mid := Function.update st (25:Fin 31) (List.replicate i true)
  have h1 : (copyOn (0:Fin 31) 25 29 (by decide) (by decide) (by decide)).Executes g st mid (5*i+2) := by
    simpa [st,mid,state] using copyOn_executes g (0:Fin 31) 25 29 (by decide) (by decide) (by decide) st rfl
  have h2 : (copyOn (1:Fin 31) 25 29 (by decide) (by decide) (by decide)).Executes g mid
      (Function.update st 25 (List.replicate (i+k) true)) (5*k+2) := by
    simpa [mid,st,state,←List.replicate_add,Nat.add_comm] using
      copyOn_executes g (1:Fin 31) 25 29 (by decide) (by decide) (by decide) mid rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma oddClock_executes (g : BitString → ℕ) (i k : ℕ) (den : BitString) :
    oddClock.Executes g (state i k den [] [] [] [] [])
      (Function.update (state i k den [] [] [] [] []) (26:Fin 31) (List.replicate (i+k+1) true)) (5*i+5*k+9) := by
  let st := state i k den [] [] [] [] []
  let mid := Function.update st (26:Fin 31) (List.replicate i true)
  let fin := Function.update st (26:Fin 31) (List.replicate (i+k) true)
  have h1 : (copyOn (0:Fin 31) 26 29 (by decide) (by decide) (by decide)).Executes g st mid (5*i+2) := by
    simpa [st,mid,state] using copyOn_executes g (0:Fin 31) 26 29 (by decide) (by decide) (by decide) st rfl
  have h2 : (copyOn (1:Fin 31) 26 29 (by decide) (by decide) (by decide)).Executes g mid fin (5*k+2) := by
    simpa [mid,fin,st,state,←List.replicate_add,Nat.add_comm] using
      copyOn_executes g (1:Fin 31) 26 29 (by decide) (by decide) (by decide) mid rfl
  have hp := push_executes g (26:Fin 31) true fin
  simp only [fin,Function.update_self,Function.update_idem,←List.replicate_succ] at hp
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 hp) using 1 <;> omega

lemma divisorClock_executes (g : BitString → ℕ) (i k : ℕ) (den f p : BitString) :
    divisorClock.Executes g (state i k den [] f p [] [])
      (Function.update (state i k den [] f p [] []) (25:Fin 31) (List.replicate (2*i+1) true)) (10*i+9) := by
  let st := state i k den [] f p [] []
  let mid := Function.update st (25:Fin 31) (List.replicate i true)
  let fin := Function.update st (25:Fin 31) (List.replicate (2*i) true)
  have h1 : (copyOn (0:Fin 31) 25 29 (by decide) (by decide) (by decide)).Executes g st mid (5*i+2) := by
    simpa [st,mid,state] using copyOn_executes g (0:Fin 31) 25 29 (by decide) (by decide) (by decide) st rfl
  have h2 : (copyOn (0:Fin 31) 25 29 (by decide) (by decide) (by decide)).Executes g mid fin (5*i+2) := by
    simpa [mid,fin,st,state,←List.replicate_add,two_mul] using
      copyOn_executes g (0:Fin 31) 25 29 (by decide) (by decide) (by decide) mid rfl
  have hp := push_executes g (25:Fin 31) true fin
  simp only [fin,Function.update_self,Function.update_idem,←List.replicate_succ] at hp
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 hp) using 1 <;> omega
end HiddenCircuits.Complexity.EvenWeightsRuntime
