import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverOuter
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverInitialize
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverFinish

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 700000
noncomputable def initializeTime : Polynomial ℕ := 200*(X+1)^3
noncomputable def finalInputP : Polynomial ℕ := 2*X+degreeP+heightP+accumulatorP+2
noncomputable def nonemptyTime : Polynomial ℕ := initializeTime+loopTime+finishTime.comp finalInputP+4
noncomputable def nonempty : OracleBlock 97 := seq initializeProgram (seq outerLoop finish)

lemma letter_stream_bound (w : WordInstance) : (encodeBitList (w.word.map letterBits)).length≤(wordBits w).length := by
  rw [wordBits_length]
  simp only [encodeBitList_length,List.length_map,List.map_map,Function.comp_def]
  omega

lemma initialize_polynomial (g : BitString → ℕ) (w : WordInstance) (rest : BitString)
    (hr : rest.length≤(wordBits w).length) :
    ∃c, initializeProgram.Executes g (Function.update (bareState w 0 0 0) 15 rest)
      (state w (Recovery.degree w+1) 0 0 0 0 (0,1) [] [] []) c ∧ c≤ initializeTime.eval (wordBits w).length := by
  obtain ⟨c,hc,hcb⟩ := initialize_executes g w rest
  refine ⟨c,hc,?_⟩
  let L := (wordBits w).length
  have hl := wordBits_length_lower w
  have hp : w.particles≤L := by dsimp [L];omega
  have hn : w.particles+w.word.length+1≤L := by dsimp [L];omega
  have hs := letter_stream_bound w
  have hd : Recovery.degree w≤L^3 := (Recovery.parameter_bounds w ⟨0,by omega⟩).1
  have hpow := Nat.pow_le_pow_left hn 3
  simp only [initializeTime,eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change c≤200*(L+1)^3
  change rest.length≤L at hr
  change (encodeBitList (w.word.map letterBits)).length≤L at hs
  have hb : c≤105*L^3+6*L+31 := by omega
  apply hb.trans
  ring_nf
  omega

lemma final_state_bound (w : WordInstance) (a : ℤ×ℤ)
    (ha : (signedBits a.1).length≤accumulatorP.eval (wordBits w).length ∧
      (signedBits a.2).length≤accumulatorP.eval (wordBits w).length) :
    ∀i,(state w 0 (Recovery.degree w+1) ((Recovery.degree w+1)*w.word.length) 0 0 a [] [] [] i).length≤
      finalInputP.eval (wordBits w).length := by
  let L := (wordBits w).length
  have hl := wordBits_length_lower w
  have hp : w.particles≤L := by dsimp [L];omega
  have hn : w.word.length≤L := by dsimp [L];omega
  have hd : Recovery.degree w≤degreeP.eval L := by simpa [L] using (Recovery.parameter_bounds w ⟨0,by omega⟩).1
  have hh : (Recovery.degree w+1)*w.word.length≤heightP.eval L := by
    calc
      _≤(degreeP.eval L+1)*L := Nat.mul_le_mul (by omega) hn
      _=heightP.eval L := by simp [heightP];ring
  change (signedBits a.1).length≤accumulatorP.eval L ∧ (signedBits a.2).length≤accumulatorP.eval L at ha
  intro i
  simp only [finalInputP,eval_add,eval_mul,eval_ofNat,eval_X]
  change _≤2*L+degreeP.eval L+heightP.eval L+accumulatorP.eval L+2
  fin_cases i <;> norm_num only [state] <;> (try simp only [ite_true,ite_false,List.length_replicate,List.length_nil]) <;> omega

 theorem nonempty_executes (g : BitString → ℕ) (w : WordInstance) (hw : w.word≠[]) (hg : CorrectOracle g w)
    (rest : BitString) (hr : rest.length≤(wordBits w).length) :
    ∃z : ℤ, ∃c, nonempty.Executes g (Function.update (bareState w 0 0 0) 15 rest)
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c≤nonemptyTime.eval (wordBits w).length := by
  obtain ⟨z,hz,hzb⟩ := word_value_bits_input w
  obtain ⟨a,ha,hab⟩ := initialize_polynomial g w rest hr
  obtain ⟨b,hb,hbb,hbits⟩ := outerLoop_executes g w hw hg
  have hnonzero := RationalAccumulator.run_nonzero (0,1) (Recovery.terms w) (by decide) (Recovery.terms_nonzero w)
  have hdiv := Recovery.accumulator_divides w hw
  obtain ⟨c,hc,hcb⟩ := finish_executes g w 0 (Recovery.degree w+1) ((Recovery.degree w+1)*w.word.length) 0 0
    (RationalAccumulator.run (0,1) (Recovery.terms w)) (finalInputP.eval (wordBits w).length)
    hnonzero hdiv (final_state_bound w _ hbits)
  have hquot : (RationalAccumulator.run (0,1) (Recovery.terms w)).1 /
      (RationalAccumulator.run (0,1) (Recovery.terms w)).2=z := by
    rw [Recovery.accumulator_exact_product w hw z hz,Int.mul_ediv_cancel _ hnonzero]
  rw [hquot] at hc
  refine ⟨z,_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),hz,?_⟩
  simp only [nonemptyTime,eval_add,eval_comp,eval_ofNat]
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
