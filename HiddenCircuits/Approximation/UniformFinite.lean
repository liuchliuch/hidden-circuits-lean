import HiddenCircuits.Approximation.SamplingComposition
namespace HiddenCircuits.Approximation.FiniteUniform
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]
noncomputable def eventProbability (A : α → Prop) : ℚ :=
  (Fintype.card {x : α // A x} : ℚ)/Fintype.card α
theorem eventProbability_nonneg (A : α → Prop) : 0 ≤ eventProbability A := by
  unfold eventProbability
  positivity
theorem eventProbability_le_one (A : α → Prop) : eventProbability A ≤ 1 := by
  by_cases h : Fintype.card α=0
  · simp [eventProbability,h]
  · have hp : (0:ℚ)<Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero h
    unfold eventProbability
    rw [div_le_one hp]
    exact_mod_cast Fintype.card_le_of_injective (fun x : {x : α // A x} => x.val) Subtype.val_injective
noncomputable def optionalProbability (A : Option α → Prop) : ℚ :=
  if Fintype.card α=0 then (if A none then 1 else 0)
  else eventProbability (fun x => A (some x))
@[simp] theorem optionalProbability_empty [IsEmpty α] (A : Option α → Prop) :
    optionalProbability A=if A none then 1 else 0 := by simp [optionalProbability]
@[simp] theorem optionalProbability_nonempty [Nonempty α] (A : Option α → Prop) :
    optionalProbability A=eventProbability (fun x => A (some x)) := by
  simp only [optionalProbability,ne_of_gt Fintype.card_pos,if_false]
theorem dyadic_split (k : ℕ) : (1/(2^(k+1) : ℚ))+(1/(2^(k+1) : ℚ))=1/(2^k : ℚ) := by
  rw [pow_succ]
  field_simp
  <;> ring
end HiddenCircuits.Approximation.FiniteUniform
