import HiddenCircuits.Compression

namespace HiddenCircuits
open scoped BigOperators

/-- Concrete permutation enumeration, avoiding noncomputable cardinality transports. -/
def finitePerms (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  ⟨permsOfList (List.finRange n),
    nodup_permsOfList (List.nodup_finRange n)⟩

 theorem finitePerms_eq_univ (n : ℕ) : finitePerms n = Finset.univ := by
  ext σ
  simp only [Finset.mem_univ, iff_true]
  exact mem_permsOfList_of_mem (fun _ _ => List.mem_finRange _)

 theorem permanent_eq_explicit {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    M.permanent = ∑ σ ∈ finitePerms n, ∏ j : Fin n, M (σ j) j := by
  rw [finitePerms_eq_univ]
  rfl

end HiddenCircuits
