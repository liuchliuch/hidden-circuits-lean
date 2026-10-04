import HiddenCircuits.Small.Gate8Perms

namespace HiddenCircuits.Small
open scoped BigOperators

def gate8NatCompound (a : Matrix (Fin 8) (Fin 8) ℕ) : Matrix (Fin 70) (Fin 70) ℕ :=
  fun s t => ∑ σ : Fin 24, ∏ j : Fin 4,
    a (gate8Tracks s (gate8PermMaps σ j)) (gate8Tracks t j)

theorem gate8_compound_cast (a : Matrix (Fin 8) (Fin 8) ℕ) :
    compress gate8Enum (compound (fun i j => (a i j : ℚ))) =
      fun s t => (gate8NatCompound a s t : ℚ) := by
  ext s t
  simp only [compress, Matrix.submatrix_apply, compound, gate8_permanent_explicit,
    gate8Enum_track, gate8NatCompound, Nat.cast_sum, Nat.cast_prod]

def gate8UpperNat : Matrix (Fin 8) (Fin 8) ℕ := fun i j => if i ≤ j then 1 else 0

theorem gate8_upper_cast : (fun i j => (gate8UpperNat i j : ℚ)) = upper 8 := by
  ext i j
  simp [gate8UpperNat, upper]

def gate8AddedNat (i : Fin 7) : Matrix (Fin 8) (Fin 8) ℕ :=
  fun a b => if a.val = i.val + 1 ∧ b.val = i.val then 1 else gate8UpperNat a b

theorem gate8_added_cast (i : Fin 7) :
    (fun a b => (gate8AddedNat i a b : ℚ)) = addedCut (n := 8) i := by
  ext a b
  simp [gate8AddedNat, addedCut, gate8UpperNat, upper]

def gate8DeletedNat (i : Fin 7) : Matrix (Fin 8) (Fin 8) ℕ :=
  fun a b => if a.val = i.val ∧ b.val = i.val then 0 else gate8UpperNat a b

theorem gate8_deleted_cast (i : Fin 7) :
    (fun a b => (gate8DeletedNat i a b : ℚ)) = deletedCut (n := 8) i := by
  ext a b
  simp [gate8DeletedNat, deletedCut, gate8UpperNat, upper]

end HiddenCircuits.Small
