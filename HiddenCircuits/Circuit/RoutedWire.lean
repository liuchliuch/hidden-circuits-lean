import HiddenCircuits.Circuit.ConstraintPrograms
import HiddenCircuits.Circuit.ConcatAssignments

namespace HiddenCircuits.Circuit

/-- Exact Boolean lookup in the three concrete regions of an explicit logical placement. -/
theorem Placement.bitAt_equiv {n d : ℕ} (p : Placement n d)
    (x : CodeBits p.before × (CodeBits d × CodeBits p.after)) (t : ℕ) :
    bitAt n (p.equiv x) t = if t<p.before then bitAt p.before x.1 t else
      if t-p.before<d then bitAt d x.2.1 (t-p.before) else
        bitAt p.after x.2.2 (t-p.before-d) := by
  change bitAt n (cast (congrArg CodeBits p.size)
    (codeConcat p.before (d+p.after) x.1 (codeConcat d p.after x.2.1 x.2.2))) t = _
  rw [bitAt_cast p.size,bitAt_concat,bitAt_concat]

 theorem localSwap_bit_zero (x : CodeBits 2) :
    bitAt 2 (wirePermutation (Equiv.swap (0:Fin 2) 1) x) 0=bitAt 2 x 1 := by
  change bitsToAssignment 2 (wirePermutation (Equiv.swap (0:Fin 2) 1) x) 0=bitsToAssignment 2 x 1
  rw [wirePermutation_bits]
  simp

 theorem localSwap_bit_one (x : CodeBits 2) :
    bitAt 2 (wirePermutation (Equiv.swap (0:Fin 2) 1) x) 1=bitAt 2 x 0 := by
  change bitsToAssignment 2 (wirePermutation (Equiv.swap (0:Fin 2) 1) x) 1=bitsToAssignment 2 x 0
  rw [wirePermutation_bits]
  simp

 theorem adjacentSwap_value {n : ℕ} (i : Fin (n-1)) (j : Fin n) :
    ((adjacentSwap i).symm j).val = if j.val=i.val then i.val+1 else if j.val=i.val+1 then i.val else j.val := by
  unfold adjacentSwap
  rw [Equiv.symm_swap]
  by_cases h0:j.val=i.val
  · have he : j=(⟨i.val,by have hi:=i.isLt;omega⟩ : Fin n) := Fin.ext h0
    rw [he,Equiv.swap_apply_left]
    simp
  · by_cases h1:j.val=i.val+1
    · have he : j=(⟨i.val+1,by have hi:=i.isLt;omega⟩ : Fin n) := Fin.ext h1
      rw [he,Equiv.swap_apply_right]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · simp [h0,h1]
      · intro he; exact h0 (congrArg Fin.val he)
      · intro he; exact h1 (congrArg Fin.val he)

/-- The lifted local exchange is exactly the actual adjacent permutation of global wire values. -/
theorem adjacentSwap_action {n : ℕ} (i : Fin (n-1))
    (x : CodeBits (adjacentPlacement i).before × (CodeBits 2 × CodeBits (adjacentPlacement i).after)) :
    wirePermutation (adjacentSwap i) ((adjacentPlacement i).equiv x) =
      (adjacentPlacement i).equiv (x.1,(wirePermutation (Equiv.swap (0:Fin 2) 1) x.2.1,x.2.2)) := by
  apply (assignmentEquiv n).injective
  funext j
  change bitsToAssignment n _ j=bitsToAssignment n _ j
  rw [wirePermutation_bits,← bitAt_eq_assignment,← bitAt_eq_assignment,
    Placement.bitAt_equiv,Placement.bitAt_equiv,adjacentSwap_value]
  simp only [adjacentPlacement]
  by_cases h0:j.val=i.val
  · simp [h0,localSwap_bit_zero]
  · by_cases h1:j.val=i.val+1
    · simp [h0,h1,localSwap_bit_one]
    · by_cases hl : j.val < i.val
      · simp [h0,h1,hl]
      · have hg : ¬ j.val-i.val<2 := by omega
        simp [h0,h1,hl,hg]

/-- The actual nine-gate macro implements the requested adjacent wire matrix in every dimension. -/
theorem adjacentSwap_lift {n : ℕ} (i : Fin (n-1)) :
    (adjacentPlacement i).lift (wireMatrix (Equiv.swap (0:Fin 2) 1))=wireMatrix (adjacentSwap i) := by
  ext x y
  obtain ⟨⟨a,⟨u,c⟩⟩,rfl⟩ := (adjacentPlacement i).equiv.surjective x
  obtain ⟨⟨b,⟨v,d⟩⟩,rfl⟩ := (adjacentPlacement i).equiv.surjective y
  rw [Placement.lift_equiv_entry]
  simp only [wireMatrix,adjacentSwap_action,(adjacentPlacement i).equiv.injective.eq_iff,Prod.mk.injEq]
  by_cases hab:a=b <;> by_cases huv:v=wirePermutation (Equiv.swap (0:Fin 2) 1) u <;>
    by_cases hcd:c=d <;> simp [hab,huv,hcd,eq_comm]

 theorem adjacentSwapProgram_matrix {n : ℕ} (i : Fin (n-1)) :
    (adjacentSwapProgram i).matrix=wireMatrix (adjacentSwap i) := by
  rw [adjacentSwapProgram_matrix_local,adjacentSwap_lift]

/-- The literal concatenated H/CZ route acts by precisely the executable adjacent-swap permutation. -/
theorem routeProgram_matrix {n : ℕ} (w : List (Fin (n-1))) :
    (routeProgram w).matrix=wireMatrix (executeSwaps w) := by
  induction w with
  | nil => rw [routeProgram,ConstraintProgram.identity_matrix]; exact (wireMatrix_one n).symm
  | cons i w ih =>
    rw [routeProgram,ConstraintProgram.compose_matrix,adjacentSwapProgram_matrix,ih,wireMatrix_mul]
    rfl

end HiddenCircuits.Circuit
