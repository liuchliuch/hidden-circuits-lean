import HiddenCircuits.GraphReduction.Runtime.UnaryCompare

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

def successorStore (x y : BitString) : Store 2 := ![x,y,[]]
noncomputable def unarySuccessor : OracleBlock 2 := seq (copyOn 0 1 2 (by decide) (by decide) (by decide)) (push 1 true)

theorem unarySuccessor_executes (g : BitString → ℕ) (n : ℕ) :
    unarySuccessor.Executes g (successorStore (List.replicate n true) [])
      (successorStore (List.replicate n true) (List.replicate (n+1) true)) (5*n+5) := by
  have h1 : (copyOn (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)).Executes g
      (successorStore (List.replicate n true) []) (successorStore (List.replicate n true) (List.replicate n true)) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (successorStore (List.replicate n true) []) rfl using 1
    · funext i; fin_cases i <;> simp [successorStore]
    · simp [successorStore]
  have h2 : (push (1 : Fin 3) true).Executes g (successorStore (List.replicate n true) (List.replicate n true))
      (successorStore (List.replicate n true) (List.replicate (n+1) true)) 1 := by
    convert push_executes g (1 : Fin 3) true (successorStore (List.replicate n true) (List.replicate n true)) using 1
    funext i; fin_cases i <;> simp [successorStore,List.replicate_succ]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma unarySuccessor_queryFree : unarySuccessor.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (push_queryFree _ _)

noncomputable def unarySuccessorOn {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : OracleBlock k := rename unarySuccessor φ
 theorem unarySuccessorOn_executes {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (n : ℕ) (hs : s∘φ=successorStore (List.replicate n true) []) :
    (unarySuccessorOn φ).Executes g s (Function.update s (φ 1) (List.replicate (n+1) true)) (5*n+5) := by
  apply rename_executes_to unarySuccessor φ g (unarySuccessor_executes g n) hs
  · have he : (Function.update s (φ 1) (List.replicate (n+1) true))∘φ = Function.update (s∘φ) 1 (List.replicate (n+1) true) := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 1).symm _ _
 lemma unarySuccessorOn_queryFree {k : ℕ} (φ : Fin 3 ↪ Fin (k+1)) : (unarySuccessorOn φ).QueryFree :=
  rename_queryFree _ _ unarySuccessor_queryFree

end HiddenCircuits.GraphReduction.Runtime
