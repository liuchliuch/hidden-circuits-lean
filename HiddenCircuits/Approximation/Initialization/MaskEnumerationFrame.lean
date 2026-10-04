import HiddenCircuits.Approximation.Initialization.MaskEnumerationSemantics

/-! The seven-stack retained-vertex emitter in an arbitrary work bank. -/
namespace HiddenCircuits.Approximation.Initialization.MaskEnumeration
open Complexity Complexity.OracleBlock

noncomputable def on {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k n : ℕ} (φ : Fin 7 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (U : Finset (Fin n))
    (hs : s ∘ φ = state (MaskEnumerationSemantics.mask U) [] [] [] [] [] []) :
    ∃ t, (on φ).Executes g s
      (Function.update (Function.update s (φ 1) (unary U.card)) (φ 4)
        (encodeBitList (List.ofFn (fun i : Fin U.card => unary (ResidualTest.vertex U i).val)))) t ∧
      t ≤ 55*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := MaskEnumerationSemantics.program_retained g U
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases r <;> rfl
  · intro r hr
    rw [Function.update_of_ne (hr 4).symm,Function.update_of_ne (hr 1).symm]

theorem on_queryFree {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.MaskEnumeration
