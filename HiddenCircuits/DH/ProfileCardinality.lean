import HiddenCircuits.DH.CographRootAgreement

/-! Sparse cardinal keys for sorting cograph profile classes, including the
complement formula and the constant outside-module contribution. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

@[simp] lemma pivotProfile_eq_inter (r x : V) :
    pivotProfile G r x = G.neighborSet r ∩ G.neighborSet x := rfl

/-- For adjacent endpoints, both endpoints already belong to the union of their
open neighborhoods, so no extra deletion terms occur in the complement formula. -/
lemma complement_pivotProfile_eq_compl_union {r x : V} (hx : G.Adj r x) :
    pivotProfile Gᶜ r x = (G.neighborSet r ∪ G.neighborSet x)ᶜ := by
  ext z
  constructor
  · rintro ⟨hrz,hxz⟩ hz
    rcases hz with hz | hz
    · exact ((G.compl_adj _ _).mp hrz).2 hz
    · exact ((G.compl_adj _ _).mp hxz).2 hz
  · intro hz
    have hrz : ¬G.Adj r z := fun h => hz (Or.inl h)
    have hxz : ¬G.Adj x z := fun h => hz (Or.inr h)
    exact ⟨(G.compl_adj _ _).mpr ⟨fun he => hxz (he ▸ hx.symm),hrz⟩,
      (G.compl_adj _ _).mpr ⟨fun he => hrz (he ▸ hx),hxz⟩⟩

/-- The executable natural-number formula adds the intersection before either
subtraction. Reordering those truncated subtractions would be incorrect. -/
theorem complement_pivotProfile_ncard [Finite V] {r x : V} (hx : G.Adj r x) :
    (pivotProfile Gᶜ r x).ncard = Nat.card V + (pivotProfile G r x).ncard -
      (G.neighborSet r).ncard - (G.neighborSet x).ncard := by
  have hU := Set.ncard_union_add_ncard_inter (G.neighborSet r) (G.neighborSet x)
  have hC := Set.ncard_add_ncard_compl (G.neighborSet r ∪ G.neighborSet x)
  rw [complement_pivotProfile_eq_compl_union hx,pivotProfile_eq_inter]
  omega

/-- Every outside-module vertex contributes equally to all profiles of its members. -/
lemma GraphModule.pivotProfile_outside {M : Set V} (hM : GraphModule G M)
    (r : V) {x y : V} (hx : x∈M) (hy : y∈M) :
    pivotProfile G r x \ M = pivotProfile G r y \ M := by
  ext z
  constructor
  · rintro ⟨hz,hzM⟩
    exact ⟨⟨hz.1,(hM x hx y hy z hzM).mp hz.2⟩,hzM⟩
  · rintro ⟨hz,hzM⟩
    exact ⟨⟨hz.1,(hM x hx y hy z hzM).mpr hz.2⟩,hzM⟩

lemma profile_partition_ncard [Finite V] (r x : V) (M : Set V) :
    (pivotProfile G r x).ncard = (pivotProfile G r x ∩ M).ncard +
      (pivotProfile G r x \ M).ncard := by
  have h := Set.ncard_diff_add_ncard_of_subset
    (show pivotProfile G r x ∩ M ⊆ pivotProfile G r x from Set.inter_subset_left)
  have he : pivotProfile G r x \ (pivotProfile G r x ∩ M) = pivotProfile G r x \ M := by
    ext z; simp only [Set.mem_diff,Set.mem_inter_iff]; tauto
  rw [he] at h
  omega

/-- Thus sorting global profile sizes sorts the relative module profiles exactly;
the outside contribution is a common additive constant, not an assumption. -/
theorem GraphModule.pivotProfile_card_le_iff [Finite V] {M : Set V}
    (hM : GraphModule G M) (r : V) {x y : V} (hx : x∈M) (hy : y∈M) :
    (pivotProfile G r x).ncard≤(pivotProfile G r y).ncard ↔
      (pivotProfile G r x ∩ M).ncard≤(pivotProfile G r y ∩ M).ncard := by
  have ho := hM.pivotProfile_outside r hx hy
  rw [profile_partition_ncard r x M,profile_partition_ncard r y M,ho]
  omega

lemma GraphModule.pivotProfile_local_subset_iff {M : Set V} (hM : GraphModule G M)
    (r : V) {x y : V} (hx : x∈M) (hy : y∈M) :
    pivotProfile G r x ⊆ pivotProfile G r y ↔
      pivotProfile G r x ∩ M ⊆ pivotProfile G r y ∩ M := by
  constructor
  · intro h z hz; exact ⟨h hz.1,hz.2⟩
  · intro h z hz
    by_cases hzM : z∈M
    · exact (h ⟨hz,hzM⟩).1
    · exact ⟨hz.1,(hM x hx y hy z hzM).mp hz.2⟩

lemma GraphModule.pivotProfile_local_eq_iff {M : Set V} (hM : GraphModule G M)
    (r : V) {x y : V} (hx : x∈M) (hy : y∈M) :
    pivotProfile G r x = pivotProfile G r y ↔
      pivotProfile G r x ∩ M = pivotProfile G r y ∩ M := by
  constructor
  · intro h; rw [h]
  · intro h
    apply Set.Subset.antisymm
    · exact (hM.pivotProfile_local_subset_iff r hx hy).mpr h.subset
    · exact (hM.pivotProfile_local_subset_iff r hy hx).mpr h.symm.subset

/-- Laminarity plus descending cardinality and distinct classes gives the exact
strict inclusion order required by the alternating staircase theorem. -/
theorem P4Free.pivotProfile_strict_of_card [Finite V] (hG : P4Free G) {r x y : V}
    (hx : x∈nonneighbors G r) (hy : y∈nonneighbors G r)
    (hcard : (pivotProfile G r y).ncard≤(pivotProfile G r x).ncard)
    (hne : pivotProfile G r x ≠ pivotProfile G r y) :
    pivotProfile G r y ⊂ pivotProfile G r x := by
  have hsub : pivotProfile G r y ⊆ pivotProfile G r x := by
    rcases hG.pivotProfiles_nested hx hy with h | h
    · exact False.elim (hne (Set.eq_of_subset_of_ncard_le h hcard))
    · exact h
  exact Set.ssubset_iff_subset_ne.mpr ⟨hsub,hne.symm⟩

end HiddenCircuits.DH
