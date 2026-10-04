import HiddenCircuits.Approximation.SamplerRuntime.SwitchSemantics
import HiddenCircuits.Approximation.Schemes

/-! Canonical successful sampler outputs and the exact finite witness set. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Output
open Complexity GraphReduction.MonotoneEndpointEncoding
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def witness (π : Equiv.Perm (Fin n)) : BitString := encodeBitList (Switch.rowWords π)
def success (π : Equiv.Perm (Fin n)) : BitString := true::witness π

@[simp] theorem decode_success (π : Equiv.Perm (Fin n)) : decodeSample (success π)=some (witness π) := rfl

theorem rowWords_injective : Function.Injective (Switch.rowWords (n:=n)) := by
  intro π ρ h
  apply Equiv.ext
  intro i
  have hh := congrArg (fun ws : List BitString => (ws[i.val]?.getD []).length) h
  simp [Switch.rowWords,rows,i.isLt] at hh
  exact Fin.ext hh

theorem witness_injective : Function.Injective (witness (n:=n)) :=
  encodeBitList_injective.comp rowWords_injective

noncomputable def witnesses (E : MonotoneEndpoints n) : Finset BitString :=
  Finset.univ.image (fun π : E.Permutations => witness π.val)

noncomputable def solutions (xs : BitString) : Finset BitString :=
  match GraphReduction.MonotoneEndpointEncoding.decode xs with
  | none => ∅
  | some E => witnesses E.2

def promised (xs : BitString) : Prop := ∃E : Input,encode E=xs

@[simp] theorem solutions_encode (E : Input) : solutions (encode E)=witnesses E.2 := by simp [solutions]

@[simp] theorem witnesses_card (E : MonotoneEndpoints n) :
    (witnesses E).card=Fintype.card E.Permutations := by
  rw [witnesses,Finset.card_image_of_injective,Finset.card_univ]
  exact fun π ρ h => Subtype.ext (witness_injective h)

theorem witnesses_nonempty (E : MonotoneEndpoints n) : (witnesses E).Nonempty ↔ Nonempty E.Permutations := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨π,hπ,he⟩ := Finset.mem_image.mp hw
    exact ⟨π⟩
  · rintro ⟨π⟩
    exact ⟨witness π.val,Finset.mem_image.mpr ⟨π,Finset.mem_univ _,rfl⟩⟩

theorem witness_mem (E : MonotoneEndpoints n) (π : E.Permutations) : witness π.val∈witnesses E := by
  exact Finset.mem_image.mpr ⟨π,Finset.mem_univ _,rfl⟩

/-- Uniformity over encoded witnesses is exactly uniformity over matchings;
injective serialization creates no padding or representation multiplicity. -/
theorem uniform_witnesses (E : MonotoneEndpoints n) (s : E.Permutations)
    (A : Option BitString → Prop) :
    uniformProbability (witnesses E) A=
      (Fintype.card {π : E.Permutations // A (some (witness π.val))}:ℚ)/Fintype.card E.Permutations := by
  classical
  letI : Nonempty E.Permutations := ⟨s⟩
  have hi : Function.Injective (fun π : E.Permutations => witness π.val) :=
    fun π ρ h => Subtype.ext (witness_injective h)
  rw [uniformProbability,witnesses_card,if_neg Fintype.card_ne_zero]
  congr 2
  rw [witnesses,Finset.filter_image,Finset.card_image_of_injective _ hi]
  simp only [Fintype.card_subtype]

@[simp] theorem count_solutions (xs : BitString) :
    (solutions xs).card=GraphReduction.MonotoneEndpointEncoding.count xs := by
  cases h : GraphReduction.MonotoneEndpointEncoding.decode xs <;>
    simp [solutions,GraphReduction.MonotoneEndpointEncoding.count,h]

end HiddenCircuits.Approximation.SamplerRuntime.Output
