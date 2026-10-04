import HiddenCircuits.Circuit.Runtime.SpectralDeltaDriverCore
import HiddenCircuits.Circuit.Runtime.SpectralDeltaLoopRuntime

/-! An unconditional physical source-array frontend and two-dimensional native
Delta oracle runtime. Bounds are polynomial in the actual input stacks; the
rational-prefix certificate is derived internally from the literal circuit. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaDriver
open Complexity OracleBlock BinaryArithmetic Polynomial SourceFrontend

noncomputable def program : OracleBlock 67 := seq front SpectralDeltaLoop.program
noncomputable def time : Polynomial ℕ := frontTime+SpectralDeltaLoop.time.comp (X+SpectralDelta.prefixBitSize)+2
noncomputable def result {n : ℕ} (w : List (ConstraintGate n)) : RationalAccumulator.Ratio :=
  RationalAccumulator.run (0,1) (SpectralDelta.items w)
def finalState {n : ℕ} (w : List (ConstraintGate n)) (acc : RationalAccumulator.Ratio) : Store 67 :=
  frame (SourceSample.store (SourceSample.canonical w 0 0 0 0) {accumulator:=acc})
    (List.replicate (Fintype.card (SpectralIndex (forbidOccurrences w))-1) true)
    (List.replicate (Fintype.card (SpectralIndex (signOccurrences w))-1) true)
lemma finalState_eq {n : ℕ} (w : List (ConstraintGate n)) (acc : RationalAccumulator.Ratio) :
    finalState w acc=SpectralDeltaLoop.state w 0 acc := rfl
@[simp] lemma finalState_low {n : ℕ} (w : List (ConstraintGate n)) (acc : RationalAccumulator.Ratio) (i : Fin 64) :
    finalState w acc (lowPort i)=SourceSample.store (SourceSample.canonical w 0 0 0 0) {accumulator:=acc} i := by
  exact frame_low _ _ _ i
lemma result_nonzero {n : ℕ} (w : List (ConstraintGate n)) : (result w).2≠0 :=
  RationalAccumulator.run_nonzero (0,1) (SpectralDelta.items w) (by decide) (SpectralDelta.items_nonzero w)
lemma result_value {n : ℕ} (w : List (ConstraintGate n)) :
    RationalAccumulator.value (result w)=constraintCircuitMatrix w (zeroBits n) (zeroBits n) := by
  rw [result,RationalAccumulator.run_value _ _ (by decide) (SpectralDelta.items_nonzero w),SpectralDelta.items_value]
  simp [RationalAccumulator.value]

set_option maxHeartbeats 600000 in
theorem program_executes (g : BitString→ℕ) (hg : DeltaOracle g) {n : ℕ} (w : List (ConstraintGate n))
    (wire : BitString) (B : ℕ) (hB : ∀i,(rawStore w 0 wire i).length≤B) :
    ∃c,program.Executes g (frame (rawStore w 0 wire) [] []) (finalState w (result w)) c ∧ c≤time.eval B := by
  obtain ⟨c1,h1,hb1⟩:=front_frame_executes g w wire B hB
  have hbit : RationalAccumulator.BitBound (SpectralDelta.prefixBitSize.eval (circuitBits n w).length) (0,1) (SpectralDelta.items w++[]) := by
    simpa using SpectralDelta.bitBound w (0,1) 0 (by norm_num)
  obtain ⟨c2,h2,hb2,hfinal⟩:=SpectralDeltaLoop.program_executes g hg w (0,1) []
    (SpectralDelta.prefixBitSize.eval (circuitBits n w).length) hbit
  have hL : (circuitBits n w).length≤B := hB 0
  have hp:=polynomial_nat_eval_mono SpectralDelta.prefixBitSize hL
  have hN : (circuitBits n w).length+SpectralDelta.prefixBitSize.eval (circuitBits n w).length≤
      B+SpectralDelta.prefixBitSize.eval B := Nat.add_le_add hL hp
  have hm:=polynomial_nat_eval_mono SpectralDeltaLoop.time hN
  dsimp only at hm
  refine ⟨_,seq_executes _ _ g h1 h2,?_⟩
  simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
  omega

theorem finalState_bound (g : BitString→ℕ) (hg : DeltaOracle g) {n : ℕ} (w : List (ConstraintGate n))
    (wire : BitString) (B : ℕ) (hB : ∀i,(rawStore w 0 wire i).length≤B) :
    ∀i,(finalState w (result w) i).length≤(X+time).eval B := by
  obtain ⟨c,hc,hcb⟩:=program_executes g hg w wire B hB
  intro i
  have h:=hc.stack_bound (frame_bound _ B hB) i
  simp only [eval_add,eval_X]
  exact h.trans (Nat.add_le_add_left hcb B)
end HiddenCircuits.Circuit.Runtime.SpectralDeltaDriver
