import HiddenCircuits.Approximation.SamplerRuntime.PartnerMoveFrame
import HiddenCircuits.Complexity.GraphVerifier.MatchingCertificates

/-! Ordinary graph-input witness sets for the actual partner sampler. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerOutput
open Complexity
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def witness (G : MatrixGraph n) (P : PerfectPartner G.graph) : BitString := PartnerMove.witness G P
def success (G : MatrixGraph n) (P : PerfectPartner G.graph) : BitString := true::witness G P

@[simp] lemma decode_success (G : MatrixGraph n) (P : PerfectPartner G.graph) :
    decodeSample (success G P)=some (witness G P) := rfl

lemma witness_injective (G : MatrixGraph n) : Function.Injective (witness G) := by
  intro P Q h
  have he := Output.witness_injective h
  apply Subtype.ext
  exact congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) he

noncomputable def witnesses (G : MatrixGraph n) : Finset BitString := Finset.univ.image (witness G)
noncomputable def solutions (raw : BitString) : Finset BitString :=
  match GraphInput.decode raw with | none => ∅ | some G => witnesses G.2

@[simp] theorem witnesses_card (G : MatrixGraph n) :
    (witnesses G).card=Fintype.card (PerfectPartner G.graph) := by
  rw [witnesses,Finset.card_image_of_injective _ (witness_injective G),Finset.card_univ]

lemma witness_mem (G : MatrixGraph n) (P : PerfectPartner G.graph) : witness G P∈witnesses G :=
  Finset.mem_image.mpr ⟨P,Finset.mem_univ _,rfl⟩

lemma witnesses_nonempty (G : MatrixGraph n) : (witnesses G).Nonempty ↔ Nonempty (PerfectPartner G.graph) := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨P,_,_⟩ := Finset.mem_image.mp hw
    exact ⟨P⟩
  · rintro ⟨P⟩
    exact ⟨witness G P,witness_mem G P⟩

theorem uniform_witnesses (G : MatrixGraph n) (P : PerfectPartner G.graph) (A : Option BitString → Prop) :
    uniformProbability (witnesses G) A=
      (Fintype.card {Q : PerfectPartner G.graph // A (some (witness G Q))}:ℚ)/Fintype.card (PerfectPartner G.graph) := by
  classical
  letI : Nonempty (PerfectPartner G.graph) := ⟨P⟩
  rw [uniformProbability,witnesses_card,if_neg Fintype.card_ne_zero]
  congr 2
  rw [witnesses,Finset.filter_image,Finset.card_image_of_injective _ (witness_injective G)]
  simp only [Fintype.card_subtype]

@[simp] lemma count_solutions (raw : BitString) : (solutions raw).card=GraphInput.perfectMatchingProblem raw := by
  cases h : GraphInput.decode raw <;>
    simp [solutions,GraphInput.perfectMatchingProblem,h,perfectMatchingCount_eq_partners]

end HiddenCircuits.Approximation.SamplerRuntime.PartnerOutput
