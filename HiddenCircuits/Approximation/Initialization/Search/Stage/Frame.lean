import HiddenCircuits.Approximation.Initialization.Search.Stage.Semantics

namespace HiddenCircuits.Approximation.Initialization.Search.Stage
open Complexity Complexity.OracleBlock SamplerRuntime

noncomputable def on {k : ℕ} (φ : Fin 51 ↪ Fin (k+1)) : OracleBlock k := rename program φ

/-- A stage changes only mask, remaining source, accumulated witness and flag. -/
def frameUpdate {k : ℕ} (φ : Fin 51 ↪ Fin (k+1)) (s : Store k)
    (mask source data ok : BitString) : Store k :=
  Function.update (Function.update (Function.update (Function.update s (φ 2) mask)
    (φ 3) source) (φ 5) data) (φ 7) ok

theorem on_executes {k : ℕ} (φ : Fin 51 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (N : ℕ) (payload mask source : BitString) (B : ℕ) (data : BitString) (L : ℕ)
    (mask' source' data' ok : BitString) (t : ℕ)
    (hs : s∘φ=state N payload mask source B data L [])
    (h : program.Executes g (state N payload mask source B data L [])
      (state N payload mask' source' B data' L ok) t) :
    (on φ).Executes g s (frameUpdate φ s mask' source' data' ok) t := by
  apply rename_executes_to program φ g h hs
  · have he : (frameUpdate φ s mask' source' data' ok)∘φ=
        Function.update (Function.update (Function.update (Function.update (s∘φ) 2 mask') 3 source') 5 data') 7 ok := by
      funext r
      simp [frameUpdate,Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext r;fin_cases r <;> rfl
  · intro r hr
    simp only [frameUpdate]
    rw [Function.update_of_ne (hr 7).symm,Function.update_of_ne (hr 5).symm,
      Function.update_of_ne (hr 3).symm,Function.update_of_ne (hr 2).symm]

theorem on_empty {k N : ℕ} (φ : Fin 51 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (source : BitString) (B : ℕ) (data : BitString) (L : ℕ)
    (hs : s∘φ=state N G.bits (MaskEnumerationSemantics.mask (∅:Finset (Fin N))) source B data L []) :
    ∃ t,(on φ).Executes g s
      (frameUpdate φ s (MaskEnumerationSemantics.mask (∅:Finset (Fin N))) source data [true]) t ∧ t≤timeBound N B L := by
  obtain ⟨t,ht,hb⟩ := program_empty g G source B data L
  exact ⟨t,on_executes φ g s N G.bits _ source B data L _ source data [true] t hs ht,hb⟩

theorem on_none {k N : ℕ} (φ : Fin 51 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (U : Finset (Fin N)) (hU : U.Nonempty) (source : BitString) (B : ℕ)
    (data : BitString) (L : ℕ)
    (hs : s∘φ=state N G.bits (MaskEnumerationSemantics.mask U) source B data L [])
    (hn : (List.finRange N).find? (CandidateTest.test G U B (TapeRead.takePadded L source) (U.min' hU))=none) :
    ∃ t,(on φ).Executes g s
      (frameUpdate φ s (MaskEnumerationSemantics.mask U) (source.drop L) data [false]) t ∧ t≤timeBound N B L := by
  obtain ⟨t,ht,hb⟩ := program_none g G U hU source B data L hn
  exact ⟨t,on_executes φ g s N G.bits _ source B data L _ _ data [false] t hs ht,hb⟩

theorem on_some {k N : ℕ} (φ : Fin 51 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (U : Finset (Fin N)) (hU : U.Nonempty) (source : BitString) (B : ℕ)
    (π : Equiv.Perm (Fin N)) (L : ℕ) (v : Fin N)
    (hs : s∘φ=state N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π) L [])
    (hv : (List.finRange N).find? (CandidateTest.test G U B (TapeRead.takePadded L source) (U.min' hU))=some v) :
    ∃ t,(on φ).Executes g s
      (frameUpdate φ s (MaskEnumerationSemantics.mask ((U.erase (U.min' hU)).erase v)) (source.drop L)
        (Output.witness (MonotoneEndpoints.transpose π (U.min' hU) v)) [true]) t ∧ t≤timeBound N B L := by
  obtain ⟨t,ht,hb⟩ := program_some g G U hU source B π L v hv
  exact ⟨t,on_executes φ g s N G.bits _ source B (Output.witness π) L _ _ _ [true] t hs ht,hb⟩

theorem on_queryFree {k : ℕ} (φ : Fin 51 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.Search.Stage
