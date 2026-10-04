import HiddenCircuits.Circuit.Runtime.SourceInnerRuntime

/-! Prepare the actual unary geometric degree, execute its
entire query row, then erase the degree before the next spectral-grid position. -/
namespace HiddenCircuits.Circuit.Runtime.SourceRow
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery

def state {k n : ℕ} (w : List (ConstraintGate n)) (a r s : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+65) :=
  FramedFor.frame (SourceWordCall.lifted (k:=k)
    (SourceSample.store (SourceSample.canonical w a r s 0) {accumulator:=acc})) []
noncomputable def result {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (acc : RationalAccumulator.Ratio) : RationalAccumulator.Ratio :=
  RationalAccumulator.run acc (SourceSampleIntegers.rowItems hn a w r s)
noncomputable def dimensions (k : ℕ) : OracleBlock (k+65) := rename
  (rename SourceSample.dimensions (SourceWordCall.lowEmbedding k)) (FramedFor.embedding (k+64))
def degreePort (k : ℕ) : Fin (k+66) := FramedFor.embedding (k+64) (SourceWordCall.lowEmbedding k 13)
noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+65) :=
  seq (dimensions k) (seq (SourceInner.program W) (clear (degreePort k)))
noncomputable def dimensionsInput : Polynomial ℕ := 4*(X+1)^2
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ :=
  SampleDimensions.time.comp dimensionsInput+SourceInner.time p+SourceQueryBounds.degreeSize+5

lemma dimensions_input_bound {n : ℕ} (w : List (ConstraintGate n)) (a C : ℕ) (r : FirstIndex w) (s : SecondIndex w) :
    forbidOccurrences w+signOccurrences w+r.val+s.val≤dimensionsInput.eval ((circuitBits n w).length+a+C) := by
  have hspec:=SampleGridBounds.spectral_bounds w r s
  have hocc:=constraintOccurrences_le_length w
  have hlen:=(SampleEmitter.circuit_size_bounds w).2
  have hpow:=Nat.pow_le_pow_left (show (circuitBits n w).length+1≤(circuitBits n w).length+a+C+1 by omega) 2
  have hL : (circuitBits n w).length≤((circuitBits n w).length+a+C+1)^2 := by nlinarith
  simp only [dimensionsInput,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one]
  omega

set_option maxHeartbeats 800000 in
theorem program_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (acc : RationalAccumulator.Ratio) (tail : List RationalAccumulator.Ratio) (C : ℕ)
    (hbit : RationalAccumulator.BitBound C acc (SourceSampleIntegers.rowItems hn a w r s++tail)) :
    ∃c,(program W).Executes g (state (k:=k) w a r.val s.val acc) (state (k:=k) w a r.val s.val (result hn a w r s acc)) c ∧
      c≤(time p).eval ((circuitBits n w).length+a+C) ∧ RationalAccumulator.BitBound C (result hn a w r s acc) tail := by
  obtain ⟨c1,h1,hb1⟩:=SourceSample.dimensions_executes g (SourceSample.canonical w a r.val s.val 0) {accumulator:=acc} rfl
  have hd : 4*r.val*forbidOccurrences w+4*s.val*signOccurrences w=degree w r.val s.val := by
    rw [SourceQueryRecovery.degree,SampleDimensions.sampled_occurrences]
    ring
  change SourceSample.dimensions.Executes g
    (SourceSample.store (SourceSample.canonical w a r.val s.val 0) {accumulator:=acc})
    (SourceSample.store (SourceSample.canonical w a r.val s.val 0)
      {accumulator:=acc,degree:=4*r.val*forbidOccurrences w+4*s.val*signOccurrences w}) c1 at h1
  rw [hd] at h1
  have h1wide:=FramedFor.lift_executes _ g _ _ [] c1 (SourceWordCall.lift_executes (k:=k) _ g _ _ c1 h1)
  obtain ⟨c2,h2,hb2,hv⟩:=SourceInner.program_executes_polynomial W g p hW hn a w r s acc tail C hbit
  have h3 : (clear (degreePort k)).Executes g
      (SourceInner.state (k:=k) w a r s 0 (result hn a w r s acc))
      (state (k:=k) w a r.val s.val (result hn a w r s acc)) (degree w r.val s.val+1) := by
    have h:=clear_executes g (degreePort k) (SourceInner.state (k:=k) w a r s 0 (result hn a w r s acc))
    convert h using 1
    · unfold degreePort SourceInner.state SourceInner.dataState SourceWordCall.lifted
      rw [FramedFor.update_body,SourceWordCall.update_low]
      change state w a r.val s.val (result hn a w r s acc)=FramedFor.frame
        (SourceWordCall.store (Function.update _ (13:Fin 64) (List.replicate 0 true)) (fun _=>[])) []
      rw [SourceSample.update_degree]
      rfl
    · simp [degreePort,SourceInner.state,SourceInner.dataState,SourceWordCall.lifted,SourceSample.store]
  refine ⟨_,seq_executes _ _ g h1wide (seq_executes _ _ g h2 h3),?_,hv⟩
  have hm:=polynomial_nat_eval_mono SampleDimensions.time (dimensions_input_bound w a C r s)
  dsimp only at hm
  have hdB:=(SourceQueryBounds.degree_bound w a r s).trans
    (polynomial_nat_eval_mono SourceQueryBounds.degreeSize (Nat.le_add_right ((circuitBits n w).length+a) C))
  dsimp only at hdB
  change c1≤SampleDimensions.time.eval (forbidOccurrences w+signOccurrences w+r.val+s.val) at hb1
  simp only [time,eval_add,eval_comp,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SourceRow
