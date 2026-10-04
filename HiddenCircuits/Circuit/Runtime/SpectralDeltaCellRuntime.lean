import HiddenCircuits.Circuit.Runtime.SpectralDeltaCellSuffix

/-! One complete native-Delta spectral sample: physical query, actual oracle
answer, integer coefficient products, online rational addition, clean work bank. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaCell
open Complexity OracleBlock BinaryArithmetic Polynomial SourceSample SourceQueryRecovery

noncomputable def program : OracleBlock 63 := seq prepare (seq call SourceSample.afterCall)
noncomputable def middleTime : Polynomial ℕ := prepareTime+callTime.comp (X+prepareTime)+2
noncomputable def time : Polynomial ℕ := middleTime+SourceSample.afterTime.comp (X+middleTime)+2

set_option maxHeartbeats 1200000 in
theorem program_executes (g : BitString→ℕ) (hg : DeltaOracle g) {n : ℕ} (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (acc : ℤ×ℤ) (B : ℕ)
    (hB : ∀i,(store (canonical w 0 r.val s.val 0) (clean acc) i).length≤B) :
    ∃c,program.Executes g (store (canonical w 0 r.val s.val 0) (clean acc))
      (store (canonical w 0 r.val s.val 0) {accumulator:=RationalAccumulator.step acc (SpectralDelta.item w r s)}) c ∧
      c≤time.eval B := by
  obtain ⟨c1,h1,hb1⟩:=prepare_executes g w r s acc B hB
  obtain ⟨c2,h2,hb2⟩:=call_executes g hg w r s acc
  have hquery:=h1.stack_bound hB (63:Fin 64)
  change (SpectralDeltaEmitter.query w r.val s.val).encode.length≤B+c1 at hquery
  have hwordBound : (SpectralDeltaEmitter.query w r.val s.val).encode.length≤B+prepareTime.eval B := by omega
  have hm:=polynomial_nat_eval_mono callTime hwordBound
  dsimp only at hm
  have hmiddle : c1+c2+2≤middleTime.eval B := by
    simp only [middleTime,eval_add,eval_comp,eval_X,eval_ofNat]
    omega
  have h12:=seq_executes _ _ g h1 h2
  have hafter : ∀i,(store (canonical w 0 r.val s.val 0) (SpectralDeltaCell.answered w r s acc) i).length≤(X+middleTime).eval B := by
    intro i
    have h:=h12.stack_bound hB i
    simp only [eval_add,eval_X]
    exact h.trans (Nat.add_le_add_left hmiddle B)
  obtain ⟨c3,h3,hb3⟩:=afterCall_executes g w r s acc ((X+middleTime).eval B) hafter
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
  simp only [eval_add,eval_X] at hb3
  omega
end HiddenCircuits.Circuit.Runtime.SpectralDeltaCell
