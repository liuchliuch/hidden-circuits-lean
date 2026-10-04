import HiddenCircuits.Approximation.Initialization.TapeWordSemantics

/-! Arbitrary-bank interface for the actual finite random-word emitter. -/
namespace HiddenCircuits.Approximation.Initialization.TapeWords
open Complexity Complexity.OracleBlock

noncomputable def on {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename program φ
theorem on_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (source : BitString) (B q : ℕ) (hs : s ∘ φ = scanState source B q []) :
    ∃ t, (on φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 0) []) (φ 2) [])
        (φ 6) (encodeBitList (words B q source))) t ∧ t ≤ q*(23*B+26)+source.length+7 := by
  obtain ⟨t,ht,hb⟩ := program_executes g source B q
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases r <;> rfl
  · intro r hr
    rw [Function.update_of_ne (hr 6).symm,Function.update_of_ne (hr 2).symm,
      Function.update_of_ne (hr 0).symm]
theorem on_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.TapeWords
