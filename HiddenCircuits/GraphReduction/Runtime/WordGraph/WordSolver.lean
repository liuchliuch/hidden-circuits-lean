import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverNonempty
import HiddenCircuits.GraphReduction.Runtime.WordGraph.EmptyWord

/-! A fixed finite signed WordEval solver using only actual Section 9 graph queries. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000
noncomputable def empty : OracleBlock 97 := rename EmptyWord.afterParse parseEmbedding
noncomputable def select : OracleBlock 97 := branchPop 15 empty nonempty nonempty
noncomputable def program : OracleBlock 97 := seq parse
  (seq (copyOn 2 15 19 (by decide) (by decide) (by decide)) select)
noncomputable def time : Polynomial ℕ := nonemptyTime+5000*(X+1)

lemma empty_executes (g : BitString → ℕ) (w : WordInstance) (hw : w.word=[]) :
    ∃c, empty.Executes g (bareState w 0 0 0) (Function.update (fun _ => []) 0 (signedBits (EmptyWord.answer w))) c ∧
      c≤2000*((wordBits w).length+1) := by
  obtain ⟨c,hc,hb⟩ := EmptyWord.afterParse_executes g w hw
  refine ⟨c,?_,hb⟩
  apply rename_executes_to EmptyWord.afterParse parseEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · clear hc hb
    intro i hi
    have hv : ¬i.val<24 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
    have h0 : i≠0 := by intro h;subst i;norm_num at hv
    simp only [bareState,hv,↓reduceDIte,Function.update_of_ne h0]

lemma select_executes (g : BitString → ℕ) (w : WordInstance) (hg : w.word≠[]→CorrectOracle g w) :
    ∃z : ℤ, ∃c, select.Executes g (Function.update (bareState w 0 0 0) 15 (List.replicate w.word.length true))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧
      c≤nonemptyTime.eval (wordBits w).length+2002*((wordBits w).length+1) := by
  by_cases hw:w.word=[]
  · obtain ⟨c,hc,hb⟩ := empty_executes g w hw
    have hi : Function.update (bareState w 0 0 0) (15:Fin 98) (List.replicate w.word.length true)=bareState w 0 0 0 := by
      rw [hw]
      change Function.update (bareState w 0 0 0) (15:Fin 98) []=bareState w 0 0 0
      exact Function.update_eq_self _ _
    refine ⟨EmptyWord.answer w,c+2,?_,(EmptyWord.answer_value w hw).symm,by omega⟩
    rw [hi]
    exact branchPop_empty (15:Fin 98) empty nonempty nonempty g rfl hc
  · have hl : 0<w.word.length := List.length_pos_iff.mpr hw
    have hinput := wordBits_length_lower w
    obtain ⟨z,c,hc,hz,hb⟩ := nonempty_executes g w hw (hg hw) (List.replicate (w.word.length-1) true)
      (by simp only [List.length_replicate];omega)
    have hclock : (Function.update (bareState w 0 0 0) (15:Fin 98) (List.replicate w.word.length true)) 15=
        true::List.replicate (w.word.length-1) true := by
      rw [Function.update_self]
      have hn : w.word.length=(w.word.length-1)+1 := by omega
      conv_lhs => rw [hn]
      rw [List.replicate_succ]
    refine ⟨z,c+2,?_,hz,by omega⟩
    apply branchPop_true (15:Fin 98) empty nonempty nonempty g hclock
    simpa only [Function.update_idem] using hc

/-- All degree clocks, graph encodings, interpolation coefficients, rational
prefixes and the final exact signed division are executed by this fixed program.
Empty words use literal mask comparison and make no graph query. -/
theorem program_executes (g : BitString → ℕ) (w : WordInstance) (hg : w.word≠[]→CorrectOracle g w) :
    ∃z : ℤ, ∃c, program.Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c≤time.eval (wordBits w).length := by
  obtain ⟨a,ha,hab⟩ := parse_executes g w
  have hcopy : (copyOn (2:Fin 98) 15 19 (by decide) (by decide) (by decide)).Executes g
      (bareState w 0 0 0) (Function.update (bareState w 0 0 0) 15 (List.replicate w.word.length true)) (5*w.word.length+2) := by
    simpa [bareState,DriverDimensions.state] using copyOn_executes g (2:Fin 98) 15 19 (by decide) (by decide) (by decide) (bareState w 0 0 0) rfl
  obtain ⟨z,b,hb,hz,hbb⟩ := select_executes g w hg
  refine ⟨z,_,seq_executes _ _ g ha (seq_executes _ _ g hcopy hb),hz,?_⟩
  have hin := wordBits_length_lower w
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
