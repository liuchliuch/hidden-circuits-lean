import HiddenCircuits.Approximation.Initialization.RawBudget
import HiddenCircuits.Approximation.Initialization.OuterLoop.Finish

/-! Exact serialization of the graph-only typed initializer. -/
namespace HiddenCircuits.Approximation.Initialization
open Complexity SamplerRuntime

noncomputable def initializerOutput {n : ℕ} (G : MatrixGraph n) (k : ℕ) (source : BitString) : BitString :=
  match RawExtraction.initialPartner G k source with
  | none => []
  | some P => PartnerOutput.success G P

lemma permutation_finish {n : ℕ} (G : MatrixGraph n) (π : Equiv.Perm (Fin n))
    (hπ : PartialPartners.Valid G.graph ∅ π) :
    PartnerMove.partnerPermutation G (PartialPartners.finish hπ)=π := by
  apply Equiv.ext
  intro v
  rfl

lemma initializerOutput_eq {n : ℕ} (G : MatrixGraph n) (k : ℕ) (source : BitString) :
    initializerOutput G k source=OuterLoop.Finish.code (RawExtraction.initialPermutation G k source) := by
  cases he : RawExtraction.initialPermutation G k source with
  | none =>
    have hh := (RawExtraction.initialPartner_none_iff G k source).mpr he
    simp [initializerOutput,hh,OuterLoop.Finish.code]
  | some π =>
    have hh : RawExtraction.initialPartner G k source=
        some (PartialPartners.finish (RawExtraction.initialPermutation_valid G k source he)) := by
      unfold RawExtraction.initialPartner
      split
      · rename_i hn
        rw [he] at hn
        cases hn
      · rename_i ρ hρ
        have hπ : ρ=π := Option.some.inj (hρ.symm.trans he)
        subst ρ
        rfl
    simp only [initializerOutput,hh,PartnerOutput.success,PartnerOutput.witness,
      PartnerMove.witness,permutation_finish,OuterLoop.Finish.code]

lemma initializerOutput_empty {n : ℕ} (G : MatrixGraph n) (k : ℕ) (source : BitString)
    (hG : ¬Nonempty (PerfectMatching G.graph)) : initializerOutput G k source=[] := by
  simp [initializerOutput,RawExtraction.initialPartner_empty G k source hG]

/-- The empty graph succeeds with a tagged empty matching, rather than failure. -/
lemma initializerOutput_zero (G : MatrixGraph 0) (k : ℕ) (source : BitString) :
    initializerOutput G k source=[true] := by
  rw [initializerOutput_eq]
  have hu : (Finset.univ : Finset (Fin 0))=∅ := by ext v;exact Fin.elim0 v
  simp [RawExtraction.initialPermutation,hu,OuterLoop.Finish.code,Output.witness,
    Switch.rowWords,GraphReduction.MonotoneEndpointEncoding.rows,encodeBitList]
end HiddenCircuits.Approximation.Initialization
