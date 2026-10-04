import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! Literal pairing, preserving the second word without copying it. -/
namespace HiddenCircuits.Complexity.PairSerialization
open OracleBlock BinaryArithmetic

def state (right left work : BitString) : Store 2 := ![right,left,work]
def wordMap : Fin 2 ↪ Fin 3 where
  toFun i := if i.val=0 then 1 else 2
  inj' := by decide +kernel
noncomputable def program : OracleBlock 2 := seq (rename wordEmitLoop wordMap)
  (seq (push 2 false) (reverseOn 2 0 (by decide)))

theorem program_executes (g : BitString → ℕ) (left right : BitString) :
    program.Executes g (state right left []) (state (pairBits left right) [] []) (10*left.length+9) := by
  have h1 : (rename wordEmitLoop wordMap).Executes g (state right left [])
      (state right [] (wordPayload left).reverse) (6*left.length+1) := by
    apply rename_executes_to _ wordMap g (wordEmitLoop_executes g left [])
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp only [List.append_nil] <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  have h2 : (push (2:Fin 3) false).Executes g (state right [] (wordPayload left).reverse)
      (state right [] (false::(wordPayload left).reverse)) 1 := by
    convert push_executes g (2:Fin 3) false (state right [] (wordPayload left).reverse) using 1
    funext i;fin_cases i <;> rfl
  have h3 : (reverseOn (2:Fin 3) 0 (by decide)).Executes g
      (state right [] (false::(wordPayload left).reverse)) (state (pairBits left right) [] [])
      (2*(1+(wordPayload left).length)+1) := by
    convert reverseOn_executes g (2:Fin 3) 0 (by decide) (state right [] (false::(wordPayload left).reverse)) using 1
    · funext i;fin_cases i <;> simp [state,pairBits_eq_payload,List.append_assoc]
    · simp [state];omega
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  have hw : (wordPayload left).length=2*left.length := by
    induction left with
    | nil => rfl
    | cons b bs ih => simp [wordPayload] at ih ⊢;omega
  omega
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ (whilePop_queryFree _ _ _ (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))
  (seq_queryFree _ _ (push_queryFree _ _) (reverseOn_queryFree _ _ _))

noncomputable def on {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (left right : BitString) (hs : s ∘ φ=state right left []) :
    (on φ).Executes g s (Function.update (Function.update s (φ 1) []) (φ 0) (pairBits left right))
      (10*left.length+9) := by
  apply rename_executes_to _ φ g (program_executes g left right) hs
  · funext i;fin_cases i <;> simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    all_goals have hh:=congrFun hs 2;simpa [Function.comp_def,state] using hh
  · intro i hi;simp [Function.update_apply,Ne.symm (hi 0),Ne.symm (hi 1)]
lemma on_queryFree {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Complexity.PairSerialization
