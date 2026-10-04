import HiddenCircuits.DH.BagMatching

/-! Finite boundary states, their genuine matching-count bounds and closed-bag interpretation. -/
namespace HiddenCircuits.DH
open scoped BigOperators
variable {V : Type*} {G : SimpleGraph V}

/-- The actual vertices not covered by an internal matching. -/
def Unmatched (p : EncodedMatching G) := {v : V // p.val v = none}

noncomputable instance (p : EncodedMatching G) : DecidableEq (Unmatched p) := Classical.decEq _

noncomputable instance [Fintype V] (p : EncodedMatching G) : Fintype (Unmatched p) := by
  classical
  unfold Unmatched
  infer_instance

lemma unmatched_card [Fintype V] (p : EncodedMatching G) :
    Fintype.card (Unmatched p) = uncovered p := by
  classical
  simp [Unmatched, Fintype.card_subtype, uncovered, Finset.sum_boole]

lemma uncovered_le_card [Fintype V] (p : EncodedMatching G) :
    uncovered p ≤ Fintype.card V := by
  rw [← unmatched_card]
  exact Fintype.card_subtype_le _

lemma uncovered_eq_zero_iff [Fintype V] (p : EncodedMatching G) :
    uncovered p = 0 ↔ ∀ v, ∃ w, p.val v = some w := by
  classical
  unfold uncovered
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h v
    cases hp : p.val v with
    | none => have := h v; simp [hp] at this
    | some w => exact ⟨w, rfl⟩
  · intro h v
    obtain ⟨w, hw⟩ := h v
    simp [hw]

lemma uncovered_zero_admissible [Fintype V] (p : EncodedMatching G)
    (h : uncovered p = 0) (T : Set V) : Admissible T p := by
  intro v hv
  obtain ⟨w, hw⟩ := (uncovered_eq_zero_iff p).mp h v
  simp [hv] at hw

/-- A closed bag's state at zero is exactly a perfect matching of its induced graph. -/
noncomputable def zeroStateEquivPerfect [Fintype V] (T : Set V) :
    BagState G T 0 ≃ PerfectMatching G where
  toFun p := ⟨p.val.toSubgraph, (p.val.toSubgraph_perfect_iff).mpr
    ((uncovered_eq_zero_iff p.val).mp p.property.2)⟩
  invFun p := ⟨p.forget.encode, uncovered_zero_admissible _
      ((uncovered_eq_zero_iff _).mpr ((encoded_perfect_correspondence G p.forget).mp p.property)) T,
    (uncovered_eq_zero_iff _).mpr ((encoded_perfect_correspondence G p.forget).mp p.property)⟩
  left_inv p := by
    apply Subtype.ext
    exact p.val.toSubgraph_encode
  right_inv p := by
    apply Subtype.ext
    exact p.forget.encode_toSubgraph

theorem zeroState_card [Fintype V] (T : Set V) :
    Fintype.card (BagState G T 0) = perfectMatchingCount G :=
  Fintype.card_congr (zeroStateEquivPerfect T)

/-- Every state counts a subset of all matchings, with an explicit global partner bound. -/
theorem bagState_card_bound [Fintype V] (T : Set V) (k : ℕ) :
    Fintype.card (BagState G T k) ≤ (Fintype.card V + 1) ^ Fintype.card V := by
  calc
    Fintype.card (BagState G T k) ≤ Fintype.card (EncodedMatching G) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card (GraphMatching G) := (Fintype.card_congr (matchingEquiv G)).symm
    _ ≤ _ := graphMatching_card_bound G

/-- Arrays have no nonzero entries beyond the number of original vertices in the bag. -/
theorem bagState_card_eq_zero_of_lt [Fintype V] (T : Set V) {k : ℕ}
    (h : Fintype.card V < k) : Fintype.card (BagState G T k) = 0 := by
  haveI : IsEmpty (BagState G T k) := ⟨fun p => by
    have hp := uncovered_le_card p.val
    rw [p.property.2] at hp
    omega⟩
  exact Fintype.card_eq_zero

end HiddenCircuits.DH
