import HiddenCircuits.Small.Gate8Definitions
import HiddenCircuits.RawCode

namespace HiddenCircuits

/-- The standard 00,01,10,11 order as actual recursively defined bit strings. -/
def twoBitLex : Fin 4 → CodeBits 2 :=
  ![(0,(0,PUnit.unit)), (0,(1,PUnit.unit)), (1,(0,PUnit.unit)), (1,(1,PUnit.unit))]

theorem twoBitLex_bijective : Function.Bijective twoBitLex := by decide +kernel

noncomputable def twoBitLexEquiv : Fin 4 ≃ CodeBits 2 :=
  Equiv.ofBijective twoBitLex twoBitLex_bijective

theorem gate8_join_val {a b u v : ℕ} (S : State a u) (T : State b v) :
    (State.join S T).val = (S.val.disjSum T.val).map finSumFinEquiv.toEmbedding := by
  ext x
  simp only [Finset.mem_map_equiv]
  have h := congrArg (fun F : Finset (Fin a ⊕ Fin b) => finSumFinEquiv.symm x ∈ F)
    (State.splitTracks_join S T)
  simpa [State.splitTracks] using Iff.of_eq h

/-- The numerical certificate's four selected rows are precisely the global raw codes. -/
theorem twoBit_rawCode : ∀ a, rawCode 2 (twoBitLex a) = twoBitCode a := by
  intro a
  apply Subtype.ext
  simp only [rawCode, balancedJoin, codeTuple, State.castParticles, gate8_join_val]
  fin_cases a <;> decide +kernel

/-- State61 has one particle in the first block, rather than the balanced two. -/
theorem gate8_tail_unbalanced : ¬ Balanced (k := 2) (Small.gate8States 61) := by
  intro h
  have hs := h 1 (by decide)
  have hc : (Small.gate8States 61).prefixCount 4 = 1 := by decide +kernel
  change (Small.gate8States 61).prefixCount 4 = 2 at hs
  omega

/-- Exact agreement of the translated global word with the two literal local filter words. -/
theorem twoBitFilterWord_global : (globalFilterWord 2 : List (Letter 8)) =
    twoBitFilterWord 0 ++ twoBitFilterWord 1 := by
  decide +kernel

theorem twoBitFilter_global : globalFilter 2 4 = twoBitFilter 0 * twoBitFilter 1 := by
  rw [twoBitFilter_sweep, globalFilter, twoBitFilterWord_global]
  norm_num

/-- The checked sixth power is exactly the global projection P₂, not a surrogate. -/
theorem twoBitProjection_global : globalProjection 2 = twoBitProjection := by
  change (globalFilter 2 4)^6 = (twoBitFilter 0 * twoBitFilter 1)^6
  rw [twoBitFilter_global]

end HiddenCircuits
