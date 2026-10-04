import HiddenCircuits.GraphReduction.Runtime.WordGraph.WideOuter
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSolver

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WideDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
open GenericDriver (terms)
set_option maxHeartbeats 700000

noncomputable def rowTime (P : Polynomial ℕ) : Polynomial ℕ :=
  5*X+(10*X+9)*Driver.heightP+12+(Driver.innerP+1)*(P+5)+Driver.innerP+7
noncomputable def loopTime (P : Polynomial ℕ) : Polynomial ℕ := (Driver.degreeP+1)*(rowTime P+5)+1
noncomputable def finalInputP (A : Polynomial ℕ) : Polynomial ℕ := 2*X+Driver.degreeP+Driver.heightP+A+2
noncomputable def nonemptyTime (A P : Polynomial ℕ) : Polynomial ℕ :=
  Driver.initializeTime+loopTime P+Driver.finishTime.comp (finalInputP A)+4
noncomputable def nonempty (B : OracleBlock 135) : OracleBlock 135 := seq (lift 38 Driver.initializeProgram) (seq (outerLoop B) (lift 38 Driver.finish))

lemma loopBound_eval (w : WordInstance) (P : Polynomial ℕ) : loopBound w (P.eval (wordBits w).length)=
    (loopTime P).eval (wordBits w).length := by
  simp [loopBound,rowBound,loopTime,rowTime]

lemma final_state_bound (w : WordInstance) (a : ℤ×ℤ) (A : Polynomial ℕ)
    (ha : (signedBits a.1).length≤A.eval (wordBits w).length ∧ (signedBits a.2).length≤A.eval (wordBits w).length) :
    ∀i,(Driver.state w 0 (Recovery.degree w+1) ((Recovery.degree w+1)*w.word.length) 0 0 a [] [] [] i).length≤
      (finalInputP A).eval (wordBits w).length := by
  let L := (wordBits w).length
  have hl := wordBits_length_lower w
  have hp : w.particles≤L := by dsimp [L];omega
  have hn : w.word.length≤L := by dsimp [L];omega
  have hd : Recovery.degree w≤Driver.degreeP.eval L := by simpa [L] using (Recovery.parameter_bounds w ⟨0,by omega⟩).1
  have hh : (Recovery.degree w+1)*w.word.length≤Driver.heightP.eval L := by
    calc
      _≤(Driver.degreeP.eval L+1)*L := Nat.mul_le_mul (by omega) hn
      _=Driver.heightP.eval L := by simp [Driver.heightP];ring
  change (signedBits a.1).length≤A.eval L ∧ (signedBits a.2).length≤A.eval L at ha
  intro i
  simp only [finalInputP,eval_add,eval_mul,eval_ofNat,eval_X]
  change _≤2*L+Driver.degreeP.eval L+Driver.heightP.eval L+A.eval L+2
  fin_cases i <;> norm_num only [Driver.state] <;>
    (try simp only [ite_true,ite_false,List.length_replicate,List.length_nil]) <;> omega

/-- This is a proof-level contract for a concrete finite target cell, never an
encoded certificate or a runtime operation. -/
def ModelSpec (B : OracleBlock 135) (g : BitString → ℕ) (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ)
    (A P : Polynomial ℕ) : Prop :=
  CellSpec B g w term (A.eval (wordBits w).length) (P.eval (wordBits w).length) ∧
  RationalAccumulator.BitBound (A.eval (wordBits w).length) (0,1) (terms w term) ∧
  (∀q,(term q).2≠0) ∧ ((terms w term).map RationalAccumulator.value).sum=w.value

theorem nonempty_executes (B : OracleBlock 135) (g : BitString → ℕ) (w : WordInstance)
    (term : Recovery.Index w → ℤ×ℤ) (A P : Polynomial ℕ) (hModel : ModelSpec B g w term A P)
    (rest : BitString) (hr : rest.length≤(wordBits w).length) :
    ∃z : ℤ, ∃c, (nonempty B).Executes g (Function.update (bareState w 0 0 0) 15 rest)
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c≤(nonemptyTime A P).eval (wordBits w).length := by
  obtain ⟨z,hz,hzb⟩ := word_value_bits_input w
  obtain ⟨a,ha,hab⟩ := Driver.initialize_polynomial g w rest hr
  obtain ⟨b,hb,hbb,hbits⟩ := outerLoop_executes B g w term _ _ hModel.1 (0,1) hModel.2.1
  rw [loopBound_eval] at hbb
  have hterms : ∀b∈terms w term,b.2≠0 := by
    intro b hb
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
    exact hModel.2.2.1 q
  have hn := RationalAccumulator.run_nonzero (0,1) (terms w term) (by decide) hterms
  have hv : RationalAccumulator.value (RationalAccumulator.run (0,1) (terms w term))=(z:ℚ) := by
    rw [RationalAccumulator.run_value _ _ (by decide) hterms,hModel.2.2.2,hz]
    norm_num [RationalAccumulator.value]
  have hden : ((RationalAccumulator.run (0,1) (terms w term)).2:ℚ)≠0 := by exact_mod_cast hn
  have he : (RationalAccumulator.run (0,1) (terms w term)).1=z*(RationalAccumulator.run (0,1) (terms w term)).2 := by
    exact_mod_cast (div_eq_iff hden).mp hv
  have hd : (RationalAccumulator.run (0,1) (terms w term)).2∣(RationalAccumulator.run (0,1) (terms w term)).1 := by
    refine ⟨z,?_⟩;rw [he];ring
  have hquot : (RationalAccumulator.run (0,1) (terms w term)).1/(RationalAccumulator.run (0,1) (terms w term)).2=z := by
    rw [he]
    exact Int.mul_ediv_cancel z hn
  obtain ⟨c,hc,hcb⟩ := Driver.finish_executes g w 0 (Recovery.degree w+1) ((Recovery.degree w+1)*w.word.length) 0 0
    (RationalAccumulator.run (0,1) (terms w term)) ((finalInputP A).eval (wordBits w).length)
    hn hd (final_state_bound w _ A hbits)
  rw [hquot] at hc
  have haW := lift_executes 38 Driver.initializeProgram g _ _ _ ha
  have hcW := lift_executes 38 Driver.finish g _ _ _ hc
  rw [extend_input] at hcW
  have hrun := seq_executes _ _ g haW (seq_executes _ _ g hb hcW)
  refine ⟨z,a+(b+c+2)+2,?_,hz,?_⟩
  · simpa only [extend_update] using hrun
  · simp only [nonemptyTime,eval_add,eval_comp,eval_ofNat]
    omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WideDriver
