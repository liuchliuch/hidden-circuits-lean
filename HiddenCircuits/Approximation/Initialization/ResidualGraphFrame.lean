import HiddenCircuits.Approximation.Initialization.ResidualGraphProgram

/-! Clean arbitrary-bank interface and ambient-size bound for the
actual mask-to-induced-graph emitter. -/
namespace HiddenCircuits.Approximation.Initialization.ResidualGraphProgram
open Complexity Complexity.OracleBlock

theorem timeBound_mono {N n n' L L' : ℕ} (hn : n ≤ n') (hL : L ≤ L') :
    timeBound N n L ≤ timeBound N n' L' := by
  unfold timeBound InducedGraphEmitter.timeBound
  gcongr

theorem uniform_bound {N : ℕ} (U : Finset (Fin N)) :
    timeBound N U.card (encodeBitList (InducedGraphEmitter.indexWords U)).length ≤
      timeBound N N (N*(2*N+2)) := by
  have hn : U.card ≤ N := by simpa using U.card_le_univ
  apply timeBound_mono hn
  exact (InducedGraphEmitter.indexWords_length_bound U).trans (Nat.mul_le_mul_right _ hn)

theorem query_length {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) :
    (GraphInput.encode ⟨U.card,InducedGraphEmitter.induced G U⟩).length = 2*U.card+U.card*U.card+1 := by
  simp [GraphInput.encode]

theorem query_length_bound {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) :
    (GraphInput.encode ⟨U.card,InducedGraphEmitter.induced G U⟩).length ≤ 2*N+N*N+1 := by
  rw [query_length]
  have hn : U.card ≤ N := by simpa using U.card_le_univ
  gcongr

noncomputable def on {k : ℕ} (φ : Fin 18 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k N : ℕ} (φ : Fin 18 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (U : Finset (Fin N))
    (hs : s ∘ φ = state N G.bits (MaskEnumerationSemantics.mask U) [] [] []) :
    ∃ t, (on φ).Executes g s
      (Function.update s (φ 3) (GraphInput.encode ⟨U.card,InducedGraphEmitter.induced G U⟩)) t ∧
      t ≤ timeBound N N (N*(2*N+2)) := by
  obtain ⟨t,ht,hb⟩ := program_executes g G U
  refine ⟨t,?_,hb.trans (uniform_bound U)⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases r <;> rfl
  · intro r hr
    exact Function.update_of_ne (hr 3).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 18 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.ResidualGraphProgram
