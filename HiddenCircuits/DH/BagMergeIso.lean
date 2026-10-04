import HiddenCircuits.DH.BagPartition
import HiddenCircuits.DH.Transport

/-! Actual induced original-graph bags split into their old fibers under a representative merge. -/
namespace HiddenCircuits.DH
variable {V R : Type*} {G : SimpleGraph V} {H : SimpleGraph R}

namespace BoundaryPartition
abbrev Fiber (p : BoundaryPartition G H) (r : R) := {a : V // p.place a = r}

def fiberGraph (p : BoundaryPartition G H) (r : R) : SimpleGraph (p.Fiber r) :=
  G.induce {a | p.place a = r}

def fiberActive (p : BoundaryPartition G H) (r : R) : Set (p.Fiber r) :=
  {a | a.val ∈ p.active}

noncomputable instance [Fintype V] (p : BoundaryPartition G H) (r : R) : Fintype (p.Fiber r) := by
  classical
  unfold Fiber
  infer_instance

abbrev MergeFiber (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v) :=
  {a : V // mergeRep u v huv (p.place a) = ⟨u,huv⟩}

noncomputable instance [Fintype V] (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v) :
    Fintype (p.MergeFiber u v huv) := by
  classical
  unfold MergeFiber
  infer_instance

lemma mergeRep_eq_survivor_iff (u v x : R) (huv : u ≠ v) :
    mergeRep u v huv x = ⟨u,huv⟩ ↔ x=u ∨ x=v := by
  classical
  by_cases hx : x = v
  · subst x
    simp
  · rw [mergeRep_surviving u v x huv hx]
    simp only [Subtype.mk.injEq,hx,or_false]

/-- The merged bag consists of precisely the two disjoint old original-vertex fibers. -/
noncomputable def mergeFiberEquiv (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v) :
    p.MergeFiber u v huv ≃ (p.Fiber u ⊕ p.Fiber v) := by
  classical
  exact {
    toFun := fun a => if ha : p.place a.val = u then .inl ⟨a.val,ha⟩ else
      .inr ⟨a.val,((mergeRep_eq_survivor_iff u v _ huv).mp a.property).resolve_left ha⟩
    invFun := fun a => match a with
      | .inl a => ⟨a.val,(mergeRep_eq_survivor_iff u v _ huv).mpr (Or.inl a.property)⟩
      | .inr a => ⟨a.val,(mergeRep_eq_survivor_iff u v _ huv).mpr (Or.inr a.property)⟩
    left_inv := by
      intro a
      dsimp only
      split_ifs <;> rfl
    right_inv := by
      intro a
      cases a with
      | inl a => simp only [dif_pos a.property]
      | inr a =>
        have ha : p.place a.val ≠ u := by rw [a.property]; exact huv.symm
        simp only [dif_neg ha] }

def mergedGraph (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v) :
    SimpleGraph (p.MergeFiber u v huv) :=
  G.induce {a | mergeRep u v huv (p.place a) = ⟨u,huv⟩}

/-- A genuine edge between representatives gives exactly the complete active cross block. -/
noncomputable def joinBagIso (p : BoundaryPartition G H) (u v : R)
    (huv : u ≠ v) (hadj : H.Adj u v) :
    joinGraph (p.fiberGraph u) (p.fiberGraph v) (p.fiberActive u) (p.fiberActive v) ≃g
      p.mergedGraph u v huv where
  toEquiv := (p.mergeFiberEquiv u v huv).symm
  map_rel_iff' := by
    rintro (a | a) (b | b)
    · rfl
    · change G.Adj a.val b.val ↔ a.val ∈ p.active ∧ b.val ∈ p.active
      rw [p.block a.val b.val (by rw [a.property,b.property]; exact huv)]
      simp only [a.property,b.property,hadj,and_true]
    · change G.Adj a.val b.val ↔ b.val ∈ p.active ∧ a.val ∈ p.active
      rw [p.block a.val b.val (by rw [a.property,b.property]; exact huv.symm)]
      simp only [a.property,b.property,hadj.symm,and_true,true_and,and_comm]
    · rfl

/-- Nonadjacent representatives have no cross-bag edges at all. -/
noncomputable def disjointBagIso (p : BoundaryPartition G H) (u v : R)
    (huv : u ≠ v) (hadj : ¬H.Adj u v) :
    disjointGraph (p.fiberGraph u) (p.fiberGraph v) ≃g p.mergedGraph u v huv where
  toEquiv := (p.mergeFiberEquiv u v huv).symm
  map_rel_iff' := by
    rintro (a | a) (b | b)
    · rfl
    · change G.Adj a.val b.val ↔ False
      rw [p.block a.val b.val (by rw [a.property,b.property]; exact huv)]
      simp only [a.property,b.property,hadj,and_false]
    · change G.Adj a.val b.val ↔ False
      rw [p.block a.val b.val (by rw [a.property,b.property]; exact huv.symm)]
      have hvu : ¬H.Adj v u := fun ha => hadj ha.symm
      simp only [a.property,b.property,hvu,and_false]
    · rfl

/-- The union of child active sets is exactly the active part of the merged original-vertex bag. -/
lemma mergeFiberEquiv_twin_active (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v) :
    (p.mergeFiberEquiv u v huv).symm ''
      {x | Sum.elim (p.fiberActive u) (p.fiberActive v) x} =
      {a : p.MergeFiber u v huv | a.val ∈ p.active} := by
  let e := (p.mergeFiberEquiv u v huv).symm
  have hm (x : p.Fiber u ⊕ p.Fiber v) :
      x ∈ {x | Sum.elim (p.fiberActive u) (p.fiberActive v) x} ↔
        (e x).val ∈ p.active := by
    cases x <;> rfl
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hm x).mp hx
  · intro ha
    refine ⟨e.symm a,(hm (e.symm a)).mpr ?_,e.apply_symm_apply a⟩
    simpa only [e.apply_symm_apply] using ha

/-- Closing the absorbed side leaves precisely the survivor's old active vertices. -/
lemma mergeFiberEquiv_pendant_active (p : BoundaryPartition G H) (u v : R) (huv : u ≠ v) :
    (p.mergeFiberEquiv u v huv).symm ''
      {x | ∃ a ∈ p.fiberActive u, x = Sum.inl a} =
      {a : p.MergeFiber u v huv | a.val ∈ p.active ∧ p.place a.val ≠ v} := by
  let e := (p.mergeFiberEquiv u v huv).symm
  have hm (x : p.Fiber u ⊕ p.Fiber v) :
      x ∈ {x | ∃ a ∈ p.fiberActive u, x = Sum.inl a} ↔
        (e x).val ∈ p.active ∧ p.place (e x).val ≠ v := by
    cases x with
    | inl a =>
      change (∃ b ∈ p.fiberActive u, Sum.inl a = Sum.inl b) ↔
        a.val ∈ p.active ∧ p.place a.val ≠ v
      simp only [Sum.inl.injEq,fiberActive,Set.mem_setOf_eq,a.property]
      constructor
      · rintro ⟨b,hb,he⟩
        exact ⟨he ▸ hb,huv⟩
      · rintro ⟨ha,_⟩
        exact ⟨a,ha,rfl⟩
    | inr a =>
      change (∃ b ∈ p.fiberActive u, Sum.inr a = Sum.inl b) ↔
        a.val ∈ p.active ∧ p.place a.val ≠ v
      simp [a.property]
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hm x).mp hx
  · intro ha
    refine ⟨e.symm a,(hm (e.symm a)).mpr ?_,e.apply_symm_apply a⟩
    simpa only [e.apply_symm_apply] using ha

/-- Actual twin-merged bag states transport to the complete-block matching model. -/
theorem twinMerge_join_count [Fintype V] (p : BoundaryPartition G H)
    {u v : R} (ht : TwinPair H u v) (hadj : H.Adj u v) (k : ℕ) :
    Fintype.card (BagState ((p.twinMerge ht).fiberGraph ⟨u,ht.distinct⟩)
      ((p.twinMerge ht).fiberActive ⟨u,ht.distinct⟩) k) =
    Fintype.card (BagState
      (joinGraph (p.fiberGraph u) (p.fiberGraph v) (p.fiberActive u) (p.fiberActive v))
      {x | Sum.elim (p.fiberActive u) (p.fiberActive v) x} k) := by
  have h := transport_bag_count (p.joinBagIso u v ht.distinct hadj)
    {x | Sum.elim (p.fiberActive u) (p.fiberActive v) x} k
  change _ = Fintype.card (BagState (p.mergedGraph u v ht.distinct)
    ((p.mergeFiberEquiv u v ht.distinct).symm '' _) k) at h
  rw [p.mergeFiberEquiv_twin_active] at h
  have hi : (p.twinMerge ht).instFintypeFiber ⟨u,ht.distinct⟩ =
      p.instFintypeMergeFiber u v ht.distinct := Subsingleton.elim _ _
  rw [hi]
  exact h.symm

/-- Actual false-twin bag states transport to the disjoint-block matching model. -/
theorem twinMerge_disjoint_count [Fintype V] (p : BoundaryPartition G H)
    {u v : R} (ht : TwinPair H u v) (hadj : ¬H.Adj u v) (k : ℕ) :
    Fintype.card (BagState ((p.twinMerge ht).fiberGraph ⟨u,ht.distinct⟩)
      ((p.twinMerge ht).fiberActive ⟨u,ht.distinct⟩) k) =
    Fintype.card (BagState (disjointGraph (p.fiberGraph u) (p.fiberGraph v))
      {x | Sum.elim (p.fiberActive u) (p.fiberActive v) x} k) := by
  have h := transport_bag_count (p.disjointBagIso u v ht.distinct hadj)
    {x | Sum.elim (p.fiberActive u) (p.fiberActive v) x} k
  change _ = Fintype.card (BagState (p.mergedGraph u v ht.distinct)
    ((p.mergeFiberEquiv u v ht.distinct).symm '' _) k) at h
  rw [p.mergeFiberEquiv_twin_active] at h
  have hi : (p.twinMerge ht).instFintypeFiber ⟨u,ht.distinct⟩ =
      p.instFintypeMergeFiber u v ht.distinct := Subsingleton.elim _ _
  rw [hi]
  exact h.symm

/-- Actual pendant bag states transport to complete-block matchings with only the survivor active. -/
theorem pendantMerge_join_count [Fintype V] (p : BoundaryPartition G H)
    {u v : R} (hp : PendantPair H u v) (k : ℕ) :
    Fintype.card (BagState ((p.pendantMerge hp).fiberGraph ⟨u,hp.distinct⟩)
      ((p.pendantMerge hp).fiberActive ⟨u,hp.distinct⟩) k) =
    Fintype.card (BagState
      (joinGraph (p.fiberGraph u) (p.fiberGraph v) (p.fiberActive u) (p.fiberActive v))
      {x | ∃ a ∈ p.fiberActive u, x = Sum.inl a} k) := by
  have h := transport_bag_count (p.joinBagIso u v hp.distinct hp.adjacent.symm)
    {x | ∃ a ∈ p.fiberActive u, x = Sum.inl a} k
  change _ = Fintype.card (BagState (p.mergedGraph u v hp.distinct)
    ((p.mergeFiberEquiv u v hp.distinct).symm '' _) k) at h
  rw [p.mergeFiberEquiv_pendant_active] at h
  have hi : (p.pendantMerge hp).instFintypeFiber ⟨u,hp.distinct⟩ =
      p.instFintypeMergeFiber u v hp.distinct := Subsingleton.elim _ _
  rw [hi]
  exact h.symm

end BoundaryPartition
end HiddenCircuits.DH
