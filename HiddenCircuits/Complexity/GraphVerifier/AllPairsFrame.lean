import HiddenCircuits.Complexity.GraphVerifier.AllPairsRuntime

/-! Complete frame for reusing the actual nested graph scan in the ordinary-input verifier. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

noncomputable def allPairsOn {k : ℕ} (φ : Fin 18 ↪ Fin (k+1)) : OracleBlock k := rename allPairsBlock φ

 theorem allPairsOn_executes {k : ℕ} (φ : Fin 18 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (n : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n≤witness.length)
    (hs : s∘φ=scanStore n 0 0 payload witness a [] []) :
    ∃ cost, (allPairsOn φ).Executes g s
      (Function.update (Function.update s (φ 1) (List.replicate n true)) (φ 5) [a && scanPairs n payload witness]) cost ∧
      cost≤28*n^4+88*n^3+117*n^2+18*n+5 := by
  obtain ⟨c,hc,hb⟩ := allPairs_executes g n payload witness a hp hw
  refine ⟨c,?_,hb⟩
  apply rename_executes_to allPairsBlock φ g hc hs
  · have he : (Function.update (Function.update s (φ 1) (List.replicate n true)) (φ 5) [a && scanPairs n payload witness])∘φ=
        Function.update (Function.update (s∘φ) 1 (List.replicate n true)) 5 [a && scanPairs n payload witness] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj
    rw [Function.update_of_ne (hj 5).symm,Function.update_of_ne (hj 1).symm]

 theorem allPairsOn_queryFree {k : ℕ} (φ : Fin 18 ↪ Fin (k+1)) : (allPairsOn φ).QueryFree :=
  rename_queryFree _ _ allPairs_queryFree

end HiddenCircuits.Complexity.GraphVerifier.Runtime
