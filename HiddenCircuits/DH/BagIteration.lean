import HiddenCircuits.DH.BagFinalization
import HiddenCircuits.DH.ColumnBounds

/-! Initialization and unchanged-fiber facts complete the local bag-state iteration invariant. -/
namespace HiddenCircuits.DH
open scoped BigOperators
variable {V R : Type*} {G : SimpleGraph V} {H : SimpleGraph R}

namespace BoundaryPartition

lemma mergeRep_eq_other_iff (u v : R) (huv : u ≠ v) (r : {r : R // r ≠ v})
    (hru : r.val ≠ u) (x : R) : mergeRep u v huv x = r ↔ x = r.val := by
  classical
  by_cases hx : x = v
  · subst x
    rw [mergeRep_deleted]
    constructor
    · intro he
      exact (hru (congrArg Subtype.val he).symm).elim
    · intro he
      exact (r.property he.symm).elim
  · rw [mergeRep_surviving u v x huv hx]
    exact Subtype.ext_iff

abbrev OtherFiber (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v)
    (r : {r : R // r ≠ v}) := {a : V // mergeRep u v huv (p.place a) = r}

noncomputable instance [Fintype V] (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v)
    (r : {r : R // r ≠ v}) : Fintype (p.OtherFiber u v huv r) := by
  classical
  unfold OtherFiber
  infer_instance

noncomputable def otherFiberEquiv (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v)
    (r : {r : R // r ≠ v}) (hru : r.val ≠ u) :
    p.Fiber r.val ≃ p.OtherFiber u v huv r where
  toFun a := ⟨a.val,(mergeRep_eq_other_iff u v huv r hru _).mpr a.property⟩
  invFun a := ⟨a.val,(mergeRep_eq_other_iff u v huv r hru _).mp a.property⟩
  left_inv a := rfl
  right_inv a := rfl

def otherGraph (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v)
    (r : {r : R // r ≠ v}) : SimpleGraph (p.OtherFiber u v huv r) :=
  G.induce {a | mergeRep u v huv (p.place a) = r}

noncomputable def otherBagIso (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v)
    (r : {r : R // r ≠ v}) (hru : r.val ≠ u) :
    p.fiberGraph r.val ≃g p.otherGraph u v huv r where
  toEquiv := p.otherFiberEquiv u v huv r hru
  map_rel_iff' := by rfl

lemma otherFiberEquiv_twin_active (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v)
    (r : {r : R // r ≠ v}) (hru : r.val ≠ u) :
    p.otherFiberEquiv u v huv r hru '' p.fiberActive r.val =
      {a : p.OtherFiber u v huv r | a.val ∈ p.active} := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro ha
    exact ⟨(p.otherFiberEquiv u v huv r hru).symm a,ha,rfl⟩

lemma otherFiberEquiv_pendant_active (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v)
    (r : {r : R // r ≠ v}) (hru : r.val ≠ u) :
    p.otherFiberEquiv u v huv r hru '' p.fiberActive r.val =
      {a : p.OtherFiber u v huv r | a.val ∈ p.active ∧ p.place a.val ≠ v} := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨hx,?_⟩
    change p.place x.val ≠ v
    rw [x.property]
    exact r.property
  · intro ha
    exact ⟨(p.otherFiberEquiv u v huv r hru).symm a,ha.1,rfl⟩

/-- The arrays of all other surviving bags stay unchanged during a twin deletion. -/
theorem twinMerge_other_count [Fintype V] (p : BoundaryPartition G H)
    {u v : R} (ht : TwinPair H u v) (r : {r : R // r ≠ v}) (hru : r.val ≠ u) (k : ℕ) :
    Fintype.card (BagState ((p.twinMerge ht).fiberGraph r) ((p.twinMerge ht).fiberActive r) k) =
      Fintype.card (BagState (p.fiberGraph r.val) (p.fiberActive r.val) k) := by
  have h := transport_bag_count (p.otherBagIso u v ht.distinct r hru) (p.fiberActive r.val) k
  change _ = Fintype.card (BagState (p.otherGraph u v ht.distinct r)
    (p.otherFiberEquiv u v ht.distinct r hru '' _) k) at h
  rw [otherFiberEquiv_twin_active] at h
  have hi : (p.twinMerge ht).instFintypeFiber r = p.instFintypeOtherFiber u v ht.distinct r :=
    Subsingleton.elim _ _
  rw [hi]
  exact h.symm

/-- Closing the absorbed pendant boundary does not alter any other bag's active vertices or states. -/
theorem pendantMerge_other_count [Fintype V] (p : BoundaryPartition G H)
    {u v : R} (hp : PendantPair H u v) (r : {r : R // r ≠ v}) (hru : r.val ≠ u) (k : ℕ) :
    Fintype.card (BagState ((p.pendantMerge hp).fiberGraph r) ((p.pendantMerge hp).fiberActive r) k) =
      Fintype.card (BagState (p.fiberGraph r.val) (p.fiberActive r.val) k) := by
  have h := transport_bag_count (p.otherBagIso u v hp.distinct r hru) (p.fiberActive r.val) k
  change _ = Fintype.card (BagState (p.otherGraph u v hp.distinct r)
    (p.otherFiberEquiv u v hp.distinct r hru '' _) k) at h
  rw [otherFiberEquiv_pendant_active] at h
  have hi : (p.pendantMerge hp).instFintypeFiber r = p.instFintypeOtherFiber u v hp.distinct r :=
    Subsingleton.elim _ _
  rw [hi]
  exact h.symm

/-- A singleton initial bag is genuinely the one-vertex edgeless graph. -/
def initialFiberIso (G : SimpleGraph V) (v : V) :
    ((initial G).fiberGraph v) ≃g (⊥ : SimpleGraph Unit) where
  toEquiv := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨v,rfl⟩
    left_inv := by intro a; apply Subtype.ext; exact a.property.symm
    right_inv := by intro a; cases a; rfl }
  map_rel_iff' := by
    intro a b
    change False ↔ G.Adj a.val b.val
    have ha : a.val = v := a.property
    have hb : b.val = v := b.property
    rw [ha,hb]
    simp

/-- The literal initial array is 1 at state one and 0 elsewhere. -/
theorem initial_count [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ) :
    Fintype.card (BagState ((initial G).fiberGraph v) ((initial G).fiberActive v) k) =
      if k=1 then 1 else 0 := by
  let e := initialFiberIso G v
  have him : e '' (Set.univ : Set ((initial G).Fiber v)) = Set.univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨a,rfl⟩ := e.toEquiv.surjective x
      exact ⟨a,Set.mem_univ _,rfl⟩
  have h := transport_bag_count e Set.univ k
  rw [him,bottom_state_card] at h
  simpa only [Fintype.card_unit,eq_comm] using h

/-- A merge's size is the sum of the actual original-vertex child-bag sizes. -/
theorem merged_card [Fintype V] (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v) :
    Fintype.card (p.MergeFiber u v huv) = Fintype.card (p.Fiber u) + Fintype.card (p.Fiber v) := by
  rw [Fintype.card_congr (p.mergeFiberEquiv u v huv),Fintype.card_sum]

end BoundaryPartition
end HiddenCircuits.DH
