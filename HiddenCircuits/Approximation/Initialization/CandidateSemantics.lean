import HiddenCircuits.Approximation.Initialization.CandidateTest

namespace HiddenCircuits.Approximation.Initialization.CandidateTest
open Complexity Complexity.OracleBlock SelfReduction FiniteChains

/- The pure soundness and child-refinement theorems are proved in CandidateTestData. -/

noncomputable def on {k : ℕ} (φ : Fin 40 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k N : ℕ} (φ : Fin 40 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString) (u v : Fin N)
    (hs : s∘φ=state N G.bits (MaskEnumerationSemantics.mask U) tape B u.val v.val [] [] []) :
    ∃ t,(on φ).Executes g s (Function.update s (φ 7) [test G U B tape u v]) t ∧
      t≤timeBound N B tape.length := by
  obtain ⟨t,ht,hb⟩ := program_executes g G U B tape u v
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 7) [test G U B tape u v])∘φ=
        Function.update (s∘φ) 7 [test G U B tape u v] := by
      funext r;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext r;fin_cases r <;> rfl
  · intro r hr
    exact Function.update_of_ne (hr 7).symm _ _

lemma on_queryFree {k : ℕ} (φ : Fin 40 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.CandidateTest
