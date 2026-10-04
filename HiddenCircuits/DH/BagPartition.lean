import HiddenCircuits.DH.JoinCounts

/-! The cross-bag structural invariant on an unchanged ordinary original graph.
Representative deletions merge fibers of the vertex-to-representative map. -/
namespace HiddenCircuits.DH

variable {V R : Type*} {G : SimpleGraph V} {H : SimpleGraph R}

/-- Bags are nonempty fibers of `place`. Every edge between different bags is exactly
an active-vertex block prescribed by the current representative graph. -/
structure BoundaryPartition (G : SimpleGraph V) (H : SimpleGraph R) where
  place : V → R
  onto : Function.Surjective place
  active : Set V
  active_nonempty : ∀ r, ∃ a, place a = r ∧ a ∈ active
  block : ∀ a b, place a ≠ place b →
    (G.Adj a b ↔ a ∈ active ∧ b ∈ active ∧ H.Adj (place a) (place b))

/-- The original graph starts with singleton bags and all vertices active. -/
def BoundaryPartition.initial (G : SimpleGraph V) : BoundaryPartition G G where
  place := id
  onto := Function.surjective_id
  active := Set.univ
  active_nonempty r := ⟨r,rfl,Set.mem_univ _⟩
  block := by intro a b h; simp

/-- Twin adjacency is required only away from the two representatives. -/
structure TwinPair (H : SimpleGraph R) (u v : R) : Prop where
  distinct : u ≠ v
  external : ∀ x, x ≠ u → x ≠ v → (H.Adj v x ↔ H.Adj u x)

/-- Pendant deletion is oriented: v is absorbed into its sole neighbor u. -/
structure PendantPair (H : SimpleGraph R) (u v : R) : Prop where
  adjacent : H.Adj v u
  unique : ∀ x, H.Adj v x → x = u

lemma PendantPair.distinct {u v : R} (h : PendantPair H u v) : u ≠ v :=
  h.adjacent.ne.symm

/-- Redirect v to u and remove v from the representative type. -/
noncomputable def mergeRep (u v : R) (huv : u ≠ v) (x : R) : {r : R // r ≠ v} := by
  classical
  exact if hx : x = v then ⟨u,huv⟩ else ⟨x,hx⟩

@[simp] lemma mergeRep_deleted (u v : R) (huv : u ≠ v) :
    mergeRep u v huv v = ⟨u,huv⟩ := by
  classical
  simp [mergeRep]

@[simp] lemma mergeRep_surviving (u v x : R) (huv : u ≠ v) (hx : x ≠ v) :
    mergeRep u v huv x = ⟨x,hx⟩ := by
  classical
  simp [mergeRep,hx]

lemma mergeRep_onto (u v : R) (huv : u ≠ v) : Function.Surjective (mergeRep u v huv) := by
  intro x
  exact ⟨x.val,mergeRep_surviving u v x.val huv x.property⟩

lemma mergeRep_ne_original {u v x y : R} {huv : u ≠ v}
    (h : mergeRep u v huv x ≠ mergeRep u v huv y) : x ≠ y := by
  intro he
  exact h (congrArg (mergeRep u v huv) he)

lemma mergeRep_ne_survivor {u v x : R} {huv : u ≠ v}
    (h : mergeRep u v huv v ≠ mergeRep u v huv x) : x ≠ u := by
  intro he
  subst x
  exact h (by rw [mergeRep_deleted,mergeRep_surviving u v u huv huv])

/-- A twin deletion preserves every adjacency between distinct surviving bags. -/
lemma TwinPair.adj_merge {u v : R} (ht : TwinPair H u v) (x y : R)
    (hxy : mergeRep u v ht.distinct x ≠ mergeRep u v ht.distinct y) :
    H.Adj x y ↔ H.Adj (mergeRep u v ht.distinct x).val (mergeRep u v ht.distinct y).val := by
  classical
  by_cases hx : x = v
  · subst x
    have hy : y ≠ v := (mergeRep_ne_original hxy).symm
    have hyu : y ≠ u := mergeRep_ne_survivor hxy
    simp only [mergeRep_deleted,mergeRep_surviving u v y ht.distinct hy]
    exact ht.external y hyu hy
  · by_cases hy : y = v
    · subst y
      have hxu : x ≠ u := mergeRep_ne_survivor hxy.symm
      simp only [mergeRep_deleted,mergeRep_surviving u v x ht.distinct hx]
      rw [H.adj_comm, H.adj_comm x u]
      exact ht.external x hxu hx
    · simp only [mergeRep_surviving u v x ht.distinct hx,
        mergeRep_surviving u v y ht.distinct hy]

/-- Twin merging preserves the structural invariant in the same unchanged original graph. -/
noncomputable def BoundaryPartition.twinMerge (p : BoundaryPartition G H)
    {u v : R} (ht : TwinPair H u v) :
    BoundaryPartition G (H.induce {r : R | r ≠ v}) where
  place a := mergeRep u v ht.distinct (p.place a)
  onto := (mergeRep_onto u v ht.distinct).comp p.onto
  active := p.active
  active_nonempty r := by
    obtain ⟨a,ha,hactive⟩ := p.active_nonempty r.val
    refine ⟨a,?_,hactive⟩
    rw [ha,mergeRep_surviving u v r.val ht.distinct r.property]
    rfl
  block a b hab := by
    rw [p.block a b (mergeRep_ne_original hab)]
    exact and_congr_right (fun _ => and_congr_right
      (fun _ => ht.adj_merge (p.place a) (p.place b) hab))

/-- A pendant deletion kills the absorbed bag's external boundary exactly. -/
lemma PendantPair.adj_merge {u v : R} (hp : PendantPair H u v) (x y : R)
    (hxy : mergeRep u v hp.distinct x ≠ mergeRep u v hp.distinct y) :
    H.Adj x y ↔ x ≠ v ∧ y ≠ v ∧
      H.Adj (mergeRep u v hp.distinct x).val (mergeRep u v hp.distinct y).val := by
  classical
  by_cases hx : x = v
  · subst x
    have hyu : y ≠ u := mergeRep_ne_survivor hxy
    simp only [ne_eq,not_true_eq_false,false_and,iff_false]
    exact fun hadj => hyu (hp.unique y hadj)
  · by_cases hy : y = v
    · subst y
      have hxu : x ≠ u := mergeRep_ne_survivor hxy.symm
      simp only [hx,ne_eq,not_true_eq_false,false_and,and_false,iff_false]
      exact fun hadj => hxu (hp.unique x hadj.symm)
    · simp only [mergeRep_surviving u v x hp.distinct hx,
        mergeRep_surviving u v y hp.distinct hy]
      exact ⟨fun ha => ⟨hx,hy,ha⟩,fun ha => ha.2.2⟩

/-- Pendant merging retains precisely the survivor's active set and preserves all external blocks. -/
noncomputable def BoundaryPartition.pendantMerge (p : BoundaryPartition G H)
    {u v : R} (hp : PendantPair H u v) :
    BoundaryPartition G (H.induce {r : R | r ≠ v}) where
  place a := mergeRep u v hp.distinct (p.place a)
  onto := (mergeRep_onto u v hp.distinct).comp p.onto
  active := {a | a ∈ p.active ∧ p.place a ≠ v}
  active_nonempty r := by
    obtain ⟨a,ha,hactive⟩ := p.active_nonempty r.val
    refine ⟨a,?_,hactive,?_⟩
    · rw [ha,mergeRep_surviving u v r.val hp.distinct r.property]
      rfl
    · rw [ha]
      exact r.property
  block a b hab := by
    rw [p.block a b (mergeRep_ne_original hab),hp.adj_merge (p.place a) (p.place b) hab]
    change _ ↔ (a ∈ p.active ∧ p.place a ≠ v) ∧
      (b ∈ p.active ∧ p.place b ≠ v) ∧ _
    tauto

end HiddenCircuits.DH
