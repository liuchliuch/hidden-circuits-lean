import HiddenCircuits.Circuit.Runtime.SourceSampleSuffix
import HiddenCircuits.Circuit.Runtime.SourceWordCall

/-! One complete real source-grid query, from clean sample
work to a clean updated rational accumulator, using a concrete signed WordEval solver. -/
namespace HiddenCircuits.Circuit.Runtime.SourceSample
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery

noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+64) :=
  seq (rename beforeCall (SourceWordCall.lowEmbedding k))
    (seq (SourceWordCall.program W) (rename afterCall (SourceWordCall.lowEmbedding k)))
noncomputable def middleTime (p : Polynomial ℕ) : Polynomial ℕ := beforeTime+(SourceWordCall.time p).comp (X+beforeTime)+2
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ := middleTime p+afterTime.comp (X+middleTime p)+2

lemma lifted_bound {k : ℕ} (s : Store 63) (B : ℕ) (hs : ∀i,(s i).length≤B) :
    ∀i,(SourceWordCall.lifted (k:=k) s i).length≤B := by
  intro i
  simp only [SourceWordCall.lifted,SourceWordCall.store]
  split_ifs
  · exact hs _
  · exact Nat.zero_le _

set_option maxHeartbeats 1000000 in
theorem program_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) (acc : ℤ×ℤ) (B : ℕ)
    (hB : ∀i,(store (canonical w a r.val s.val u.val) {accumulator:=acc,degree:=degree w r.val s.val} i).length≤B) :
    ∃z : ℤ,∃c,(program W).Executes g
      (SourceWordCall.lifted (store (canonical w a r.val s.val u.val) {accumulator:=acc,degree:=degree w r.val s.val}))
      (SourceWordCall.lifted (store (canonical w a r.val s.val u.val)
        {accumulator:=RationalAccumulator.step acc (item a w r s u z),degree:=degree w r.val s.val})) c ∧
      (word hn w r s u).value=(z:ℚ) ∧ c≤(time p).eval B := by
  let param:=canonical w a r.val s.val u.val
  let v0 : Values:={accumulator:=acc,degree:=degree w r.val s.val}
  obtain ⟨c1,h1,hb1⟩:=beforeCall_executes g hn w a r s u acc B hB
  have h1wide:=SourceWordCall.lift_executes (k:=k) beforeCall g _ _ c1 h1
  obtain ⟨z,c2,h2,hz,hb2⟩:=SourceWordCall.program_executes W g p hW (word hn w r s u)
    (store param (prepared hn w a r s u acc)) rfl rfl rfl
  rw [update_query,update_answer] at h2
  change (SourceWordCall.program W).Executes g (SourceWordCall.lifted (store param (prepared hn w a r s u acc)))
    (SourceWordCall.lifted (store param (answered hn w a r s u acc z))) c2 at h2
  have hquery:=h1.stack_bound hB (63:Fin 64)
  change (wordBits (word hn w r s u)).length≤B+c1 at hquery
  have hwordBound : (wordBits (word hn w r s u)).length≤B+beforeTime.eval B := by omega
  have hm:=polynomial_nat_eval_mono (SourceWordCall.time p) hwordBound
  dsimp only at hm
  have hmiddle : c1+c2+2≤(middleTime p).eval B := by
    simp only [middleTime,eval_add,eval_comp,eval_X,eval_ofNat]
    omega
  have h12:=seq_executes _ _ g h1wide h2
  have hsize:=h12.stack_bound (lifted_bound (k:=k) _ B hB)
  have hafter : ∀i,(store param (answered hn w a r s u acc z) i).length≤(X+middleTime p).eval B := by
    intro i
    have h:=hsize (SourceWordCall.lowEmbedding k i)
    change (SourceWordCall.lifted (store param (answered hn w a r s u acc z)) (SourceWordCall.lowEmbedding k i)).length≤B+(c1+c2+2) at h
    simp only [SourceWordCall.lifted,SourceWordCall.store_low] at h
    simp only [eval_add,eval_X]
    omega
  obtain ⟨c3,h3,hb3⟩:=afterCall_executes g hn w a r s u acc z ((X+middleTime p).eval B) hafter
  have h3wide:=SourceWordCall.lift_executes (k:=k) afterCall g _ _ c3 h3
  refine ⟨z,_,seq_executes _ _ g h1wide (seq_executes _ _ g h2 h3wide),hz,?_⟩
  simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
  simp only [eval_add,eval_X] at hb3
  omega
end HiddenCircuits.Circuit.Runtime.SourceSample
