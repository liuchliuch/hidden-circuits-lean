import HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericFinish

/-! Fixed source/loop/result machinery parameterized only by an actual finite
target cell. Final target theorems instantiate and discharge ModelSpec. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 600000
noncomputable def select (B : OracleBlock 97) : OracleBlock 97 := branchPop 15 Driver.empty (nonempty B) (nonempty B)
noncomputable def program (B : OracleBlock 97) : OracleBlock 97 := seq Driver.parse
  (seq (copyOn 2 15 19 (by decide) (by decide) (by decide)) (select B))
noncomputable def time (A P : Polynomial ℕ) : Polynomial ℕ := nonemptyTime A P+5000*(X+1)

lemma select_executes (B : OracleBlock 97) (g : BitString → ℕ) (w : WordInstance)
    (term : Recovery.Index w → ℤ×ℤ) (A P : Polynomial ℕ) (hModel : w.word≠[]→ModelSpec B g w term A P) :
    ∃z : ℤ, ∃c, (select B).Executes g (Function.update (Driver.bareState w 0 0 0) 15 (List.replicate w.word.length true))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧
      c≤(nonemptyTime A P).eval (wordBits w).length+2002*((wordBits w).length+1) := by
  by_cases hw:w.word=[]
  · obtain ⟨c,hc,hb⟩ := Driver.empty_executes g w hw
    have hi : Function.update (Driver.bareState w 0 0 0) (15:Fin 98) (List.replicate w.word.length true)=Driver.bareState w 0 0 0 := by
      rw [hw]
      change Function.update (Driver.bareState w 0 0 0) (15:Fin 98) []=Driver.bareState w 0 0 0
      exact Function.update_eq_self _ _
    refine ⟨EmptyWord.answer w,c+2,?_,(EmptyWord.answer_value w hw).symm,by omega⟩
    rw [hi]
    exact branchPop_empty (15:Fin 98) Driver.empty (nonempty B) (nonempty B) g rfl hc
  · have hl : 0<w.word.length := List.length_pos_iff.mpr hw
    have hinput := wordBits_length_lower w
    obtain ⟨z,c,hc,hz,hb⟩ := nonempty_executes B g w term A P (hModel hw) (List.replicate (w.word.length-1) true)
      (by simp only [List.length_replicate];omega)
    have hclock : (Function.update (Driver.bareState w 0 0 0) (15:Fin 98) (List.replicate w.word.length true)) 15=
        true::List.replicate (w.word.length-1) true := by
      rw [Function.update_self]
      have hn : w.word.length=(w.word.length-1)+1 := by omega
      conv_lhs => rw [hn]
      rw [List.replicate_succ]
    refine ⟨z,c+2,?_,hz,by omega⟩
    apply branchPop_true (15:Fin 98) Driver.empty (nonempty B) (nonempty B) g hclock
    simpa only [Function.update_idem] using hc

theorem program_executes (B : OracleBlock 97) (g : BitString → ℕ) (w : WordInstance)
    (term : Recovery.Index w → ℤ×ℤ) (A P : Polynomial ℕ) (hModel : w.word≠[]→ModelSpec B g w term A P) :
    ∃z : ℤ, ∃c, (program B).Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c≤(time A P).eval (wordBits w).length := by
  obtain ⟨a,ha,hab⟩ := Driver.parse_executes g w
  have hcopy : (copyOn (2:Fin 98) 15 19 (by decide) (by decide) (by decide)).Executes g
      (Driver.bareState w 0 0 0) (Function.update (Driver.bareState w 0 0 0) 15 (List.replicate w.word.length true)) (5*w.word.length+2) := by
    simpa [Driver.bareState,DriverDimensions.state] using copyOn_executes g (2:Fin 98) 15 19 (by decide) (by decide) (by decide) (Driver.bareState w 0 0 0) rfl
  obtain ⟨z,b,hb,hz,hbb⟩ := select_executes B g w term A P hModel
  refine ⟨z,_,seq_executes _ _ g ha (seq_executes _ _ g hcopy hb),hz,?_⟩
  have hin := wordBits_length_lower w
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericDriver
