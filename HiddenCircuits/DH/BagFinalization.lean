import HiddenCircuits.DH.BagMergeIso
import HiddenCircuits.DH.BagBounds

/-! Finalizing an isolated representative factors perfect matchings of the actual original graph. -/
namespace HiddenCircuits.DH
open scoped BigOperators
variable {V W R : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma perfectMatchingCount_iso [Fintype V] [Fintype W] (e : G ≃g H) :
    perfectMatchingCount G = perfectMatchingCount H := by
  have h := transport_bag_count e Set.univ 0
  simpa only [zeroState_card] using h

lemma perfectMatchingCount_disjoint [Fintype V] [Fintype W] :
    perfectMatchingCount (disjointGraph G H) = perfectMatchingCount G * perfectMatchingCount H := by
  rw [← zeroState_card (G := disjointGraph G H) {x | Sum.elim (Set.univ : Set V) Set.univ x},
    falseTwin_count]
  change (∑ i : Fin 1, Fintype.card (BagState G Set.univ i.val) *
    Fintype.card (BagState H Set.univ (0-i.val))) = _
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero,Nat.sub_zero,zeroState_card]

namespace BoundaryPartition
variable {K : SimpleGraph R}

abbrev Outside (p : BoundaryPartition G K) (u : R) := {a : V // p.place a ≠ u}

def remainingGraph (p : BoundaryPartition G K) (u : R) : SimpleGraph (p.Outside u) :=
  G.induce {a | p.place a ≠ u}

noncomputable instance [Fintype V] (p : BoundaryPartition G K) (u : R) : Fintype (p.Outside u) := by
  classical
  unfold Outside
  infer_instance

/-- Removing an entire finalized original-vertex bag preserves the remaining partition. -/
def finalize (p : BoundaryPartition G K) (u : R) :
    BoundaryPartition (p.remainingGraph u) (K.induce {r | r ≠ u}) where
  place a := ⟨p.place a.val,a.property⟩
  onto r := by
    obtain ⟨a,ha⟩ := p.onto r.val
    refine ⟨⟨a,?_⟩,?_⟩
    · rw [ha]; exact r.property
    · exact Subtype.ext ha
  active := {a | a.val ∈ p.active}
  active_nonempty r := by
    obtain ⟨a,ha,hactive⟩ := p.active_nonempty r.val
    refine ⟨⟨a,?_⟩,Subtype.ext ha,hactive⟩
    rw [ha]; exact r.property
  block a b hab := by
    exact p.block a.val b.val (fun he => hab (Subtype.ext he))

lemma isolated_no_cross (p : BoundaryPartition G K) (u : R)
    (hu : ∀ r, ¬K.Adj u r) (a : p.Fiber u) (b : p.Outside u) : ¬G.Adj a.val b.val := by
  intro hab
  have hplace : p.place a.val ≠ p.place b.val := by rw [a.property]; exact b.property.symm
  have hrep := ((p.block a.val b.val hplace).mp hab).2.2
  rw [a.property] at hrep
  exact hu _ hrep

/-- An isolated representative's induced bag is a true disjoint component of the current graph. -/
noncomputable def isolatedBagIso (p : BoundaryPartition G K) (u : R)
    (hu : ∀ r, ¬K.Adj u r) :
    disjointGraph (p.fiberGraph u) (p.remainingGraph u) ≃g G := by
  classical
  exact {
    toEquiv := Equiv.sumCompl (fun a => p.place a = u)
    map_rel_iff' := by
      rintro (a | a) (b | b)
      · rfl
      · change G.Adj a.val b.val ↔ False
        exact iff_false_intro (p.isolated_no_cross u hu a b)
      · change G.Adj a.val b.val ↔ False
        exact iff_false_intro (fun h => p.isolated_no_cross u hu b a h.symm)
      · rfl }

/-- The algorithm's multiplication on finalization is an exact factorization of actual PMs. -/
theorem finalize_count [Fintype V] (p : BoundaryPartition G K) (u : R)
    (hu : ∀ r, ¬K.Adj u r) :
    perfectMatchingCount G =
      Fintype.card (BagState (p.fiberGraph u) (p.fiberActive u) 0) *
        perfectMatchingCount (p.remainingGraph u) := by
  rw [zeroState_card]
  rw [← perfectMatchingCount_iso (p.isolatedBagIso u hu),perfectMatchingCount_disjoint]

end BoundaryPartition
end HiddenCircuits.DH
