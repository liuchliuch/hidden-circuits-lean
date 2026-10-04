import HiddenCircuits.GlobalFilter
import HiddenCircuits.BlockFlow

/-! Concrete boundary-flow support and its polynomially bounded potential for the
actual concatenated global filter word. -/
namespace HiddenCircuits
open scoped BigOperators

/-- No letter in the literal concatenated filter crosses a four-track block boundary. -/
theorem globalFilterWord_internal_index (k : ℕ) :
    ∀ l ∈ globalFilterWord k, (l.index.val+1) % 4 ≠ 0 := by
  induction k with
  | zero => simp [globalFilterWord]
  | succ k ih =>
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨l,_,rfl⟩ := List.mem_map.mp hl
      have hi := l.index.isLt
      simp only [Letter.inLeft,leftIndex]
      omega
    · obtain ⟨l₀,h₀,he⟩ := List.mem_map.mp hl
      subst l
      have hh := ih l₀ h₀
      simpa only [Letter.inRight,rightIndex,Nat.add_assoc,Nat.add_mod,
        Nat.mod_self,Nat.zero_add,Nat.mod_mod] using hh

/-- Every four-track block boundary has one-way flow in the literal word. -/
theorem globalFilterWord_prefix_boundary {k q : ℕ} (S T : State (blockWidth k) q)
    (h : wordMatrix q (globalFilterWord k) S T ≠ 0) (j : ℕ) :
    T.prefixCount (4*j) ≤ S.prefixCount (4*j) := by
  apply word_prefix_outside (globalFilterWord k) (4*j) _ S T h
  intro l hl he
  apply globalFilterWord_internal_index k l hl
  rw [← he]
  omega

/-- Scalar normalization does not create new support. -/
theorem globalFilter_prefix_boundary {k q : ℕ} (S T : State (blockWidth k) q)
    (h : globalFilter k q S T ≠ 0) (j : ℕ) :
    T.prefixCount (4*j) ≤ S.prefixCount (4*j) := by
  apply globalFilterWord_prefix_boundary S T _ j
  intro hz
  apply h
  simp [globalFilter, hz]

namespace State
/-- An occupied prefix contains at most the total number of occupied tracks. -/
theorem prefixCount_le_particles {n q : ℕ} (S : State n q) (c : ℕ) :
    S.prefixCount c ≤ q := by
  rw [prefix_card]
  calc
    (S.val.filter (fun x => x.val < c)).card ≤ S.val.card := Finset.card_filter_le _ _
    _ = q := S.property

@[simp] theorem prefixCount_total {n q : ℕ} (S : State n q) :
    S.prefixCount n = q := by
  simp [prefixCount,S.property]

/-- The bounded integer potential measuring rightward flow across all internal block cuts. -/
def boundaryPotential {k q : ℕ} (S : State (blockWidth k) q) : ℕ :=
  ∑ j : Fin (k-1), (q - S.prefixCount (4*(j.val+1)))

 theorem boundaryPotential_upper {k q : ℕ} (S : State (blockWidth k) q) :
    S.boundaryPotential ≤ q*(k-1) := by
  have hh := Finset.sum_le_sum (s:=Finset.univ)
    (fun (j : Fin (k-1)) _ => Nat.sub_le q (S.prefixCount (4*(j.val+1))))
  simpa only [boundaryPotential,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.mul_comm] using hh

 theorem boundaryPotential_lower {k q : ℕ} (S : State (blockWidth k) q) :
    0 ≤ S.boundaryPotential := Nat.zero_le _
end State

/-- Every actual nonzero global-filter entry is monotone for the bounded potential. -/
theorem globalFilter_potential_le {k q : ℕ} (S T : State (blockWidth k) q)
    (h : globalFilter k q S T ≠ 0) : S.boundaryPotential ≤ T.boundaryPotential := by
  apply Finset.sum_le_sum
  intro j _
  have hh := globalFilter_prefix_boundary S T h (j.val+1)
  omega

/-- Equality of the potential is exactly equality at every internal block boundary,
for an actual nonzero global-filter entry. -/
theorem globalFilter_potential_eq_iff {k q : ℕ} (S T : State (blockWidth k) q)
    (h : globalFilter k q S T ≠ 0) :
    S.boundaryPotential = T.boundaryPotential ↔
      ∀ j : Fin (k-1), S.prefixCount (4*(j.val+1)) = T.prefixCount (4*(j.val+1)) := by
  constructor
  · intro he j
    have hmono : ∀ j ∈ (Finset.univ : Finset (Fin (k-1))),
        q-S.prefixCount (4*(j.val+1)) ≤ q-T.prefixCount (4*(j.val+1)) := by
      intro j _
      have hh := globalFilter_prefix_boundary S T h (j.val+1)
      omega
    have heach := (Finset.sum_eq_sum_iff_of_le hmono).mp he j (Finset.mem_univ j)
    have hS := S.prefixCount_le_particles (4*(j.val+1))
    have hT := T.prefixCount_le_particles (4*(j.val+1))
    omega
  · intro he
    apply Finset.sum_congr rfl
    intro j _
    rw [he j]

/-- Unless all internal prefix counts agree, an actual transition advances by at
least one integer unit. This is the strict-support input for stabilization. -/
theorem globalFilter_potential_strict {k q : ℕ} (S T : State (blockWidth k) q)
    (h : globalFilter k q S T ≠ 0)
    (hne : ¬ ∀ j : Fin (k-1), S.prefixCount (4*(j.val+1)) = T.prefixCount (4*(j.val+1))) :
    S.boundaryPotential + 1 ≤ T.boundaryPotential := by
  have hle := globalFilter_potential_le S T h
  have hne' : S.boundaryPotential ≠ T.boundaryPotential :=
    fun he => hne ((globalFilter_potential_eq_iff S T h).mp he)
  omega

/-- Equivalent boundary-equality criterion including the two trivial endpoint cuts.
This form matches the block-count equivalence relation used for diagonal sectors. -/
theorem globalFilter_potential_eq_iff_all {k q : ℕ} (S T : State (blockWidth k) q)
    (h : globalFilter k q S T ≠ 0) :
    S.boundaryPotential = T.boundaryPotential ↔
      ∀ j : ℕ, j ≤ k → S.prefixCount (4*j) = T.prefixCount (4*j) := by
  rw [globalFilter_potential_eq_iff S T h]
  constructor
  · intro he j hj
    by_cases hj0 : j = 0
    · subst j
      simp [State.prefixCount]
    by_cases hjk : j = k
    · subst j
      rw [← blockWidth_eq k,State.prefixCount_total,State.prefixCount_total]
    have hlt : j-1 < k-1 := by omega
    let r : Fin (k-1) := ⟨j-1,hlt⟩
    have hr : r.val+1 = j := by dsimp [r]; omega
    simpa only [hr] using he r
  · intro he j
    exact he (j.val+1) (by have hh := j.isLt; omega)

 theorem globalFilter_potential_strict_of_prefix_ne {k q : ℕ}
    (S T : State (blockWidth k) q) (h : globalFilter k q S T ≠ 0)
    (hne : ¬ ∀ j : ℕ, j ≤ k → S.prefixCount (4*j) = T.prefixCount (4*j)) :
    S.boundaryPotential + 1 ≤ T.boundaryPotential := by
  have hle := globalFilter_potential_le S T h
  have hne' : S.boundaryPotential ≠ T.boundaryPotential :=
    fun he => hne ((globalFilter_potential_eq_iff_all S T h).mp he)
  omega

end HiddenCircuits
