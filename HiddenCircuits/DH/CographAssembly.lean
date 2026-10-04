import HiddenCircuits.DH.CographExtraction
import HiddenCircuits.DH.CographEnvelopes

/-! Graph-level assembly of the two kinds of recursive cograph profile cells. -/
namespace HiddenCircuits.DH
open SimpleGraph CographStaircase
variable {V : Type*} {G : SimpleGraph V}

def branchHead : (V ⊕ V) → V
  | .inl x => x
  | .inr x => x

def branchCell (G : SimpleGraph V) (M : Set V) (r : V) : (V ⊕ V) → Set V
  | .inl x => relativePivotCell G M r x
  | .inr x => relativePivotCell Gᶜ M r x

lemma P4Free.branchCell_module (hG : P4Free G) {M : Set V} (hM : GraphModule G M)
    (r : V) (x : V ⊕ V) : GraphModule G (branchCell G M r x) := by
  cases x with
  | inl x => exact hG.relativePivotCell_module hM r x
  | inr x => exact graphModule_compl_iff.mp (hG.compl.relativePivotCell_module hM.compl r x)

lemma branchCell_root_out (M : Set V) (r : V) (x : V ⊕ V) : r∉branchCell G M r x := by
  cases x <;> intro h <;> exact h.2.1.1 rfl

lemma branchCell_root_adj {M : Set V} {r a : V} {x : V ⊕ V}
    (ha : a∈branchCell G M r x) : G.Adj r a ↔ joined x=true := by
  cases x with
  | inl x => exact iff_of_false ha.2.1.2 Bool.false_ne_true
  | inr x =>
    have h : a∈nonneighbors Gᶜ r := ha.2.1
    rw [nonneighbors_compl] at h
    exact iff_of_true h rfl

/-- The staircase quotient has exactly the adjacency of any pair of vertices in
its disjoint branch cells, not just the adjacency of the chosen representatives. -/
theorem P4Free.branchCell_cross (hG : P4Free G) {M : Set V} (hM : GraphModule G M)
    {r : V} {x y : V ⊕ V} (hx : branchHead x∈branchCell G M r x)
    (hy : branchHead y∈branchCell G M r y) (hd : Disjoint (branchCell G M r x) (branchCell G M r y))
    {a b : V} (ha : a∈branchCell G M r x) (hb : b∈branchCell G M r y) :
    G.Adj a b ↔ cross G.Adj x y := by
  have hxy := (hG.branchCell_module hM r x).cross_uniform (hG.branchCell_module hM r y) hd ha hx hb hy
  apply hxy.trans
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      apply iff_false_intro
      intro he
      have hp := hG.pivotProfile_eq_of_edge hx.2.1 hy.2.1 he
      exact Set.disjoint_left.mp hd ⟨hy.1,hy.2.1,hp.symm⟩ hy
    | inr y => rfl
  | inr x =>
    cases y with
    | inl y => exact G.adj_comm x y
    | inr y =>
      apply iff_true_intro
      by_contra he
      have hne : x≠y := fun heq => Set.disjoint_left.mp hd (heq ▸ hx) hy
      have hcomp : Gᶜ.Adj x y := (G.compl_adj _ _).mpr ⟨hne,he⟩
      have hp := hG.compl.pivotProfile_eq_of_edge hx.2.1 hy.2.1 hcomp
      exact Set.disjoint_left.mp hd ⟨hy.1,hy.2.1,hp.symm⟩ hy

lemma branchCells_opposite_disjoint (G : SimpleGraph V) (M : Set V) (r x y : V) :
    Disjoint (branchCell G M r (.inl x)) (branchCell G M r (.inr y)) := by
  apply Set.disjoint_left.mpr
  intro z hx hy
  have hz : z∈nonneighbors Gᶜ r := hy.2.1
  rw [nonneighbors_compl] at hz
  exact hx.2.1.2 hz

/-- Strict profile order prevents duplicate or overlapping recursive branches. -/
theorem branchCells_weave_disjoint (G : SimpleGraph V) (M : Set V) (r : V)
    (s : Bool) (as bs : List V)
    (ha : as.Pairwise (fun x y => pivotProfile G r y ⊂ pivotProfile G r x))
    (hb : bs.Pairwise (fun x y => pivotProfile Gᶜ r y ⊂ pivotProfile Gᶜ r x)) :
    (weave s as bs).Pairwise (fun x y => Disjoint (branchCell G M r x) (branchCell G M r y)) := by
  apply weave_pairwise
  · apply ha.imp
    intro x y h
    apply Set.disjoint_left.mpr
    intro z hx hy
    exact h.ne (hy.2.2.symm.trans hx.2.2)
  · apply hb.imp
    intro x y h
    apply Set.disjoint_left.mpr
    intro z hx hy
    exact h.ne (hy.2.2.symm.trans hx.2.2)
  · intro x hx y hy
    exact ⟨branchCells_opposite_disjoint G M r x y,(branchCells_opposite_disjoint G M r x y).symm⟩

/-- The runtime constructor only alternates the supplied child heads, constructs
each child once, and attaches it with the branch's union/join tag. -/
def assembleCograph (r : V) (s : Bool) (as bs : List V)
    (child : (V ⊕ V) → LabeledCographTree V) : LabeledCographTree V :=
  LabeledCographTree.attach (.leaf r)
    ((weave s as bs).map (fun h => (joined h,child h)))

/-- Exact graph reconstruction from the two profile-cell families. The premises
are local semantic consequences of the verified sweep/envelope invariants. -/
theorem P4Free.assembleCograph_correct (hG : P4Free G) {M : Set V} (hM : GraphModule G M)
    (r : V) (s : Bool) (as bs : List V) (child : (V ⊕ V) → LabeledCographTree V)
    (hheads : ∀h∈weave s as bs, branchHead h∈branchCell G M r h)
    (hchild : ∀h∈weave s as bs, LabeledCographTree.Correct G (child h))
    (hleaves : ∀h∈weave s as bs, ∀v, v∈(child h).leaves ↔ v∈branchCell G M r h)
    (hdisjoint : (weave s as bs).Pairwise (fun x y => Disjoint (branchCell G M r x) (branchCell G M r y)))
    (hcross : (weave s as bs).Pairwise (fun x y => cross G.Adj x y ↔ joined y=true)) :
    LabeledCographTree.Correct G (assembleCograph r s as bs child) := by
  apply LabeledCographTree.correct_attach
  · exact LabeledCographTree.correct_leaf G r
  · intro p hp
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hp
    exact hchild h hh
  · intro p hp x hx y hy
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hp
    have hxr : x=r := by simpa [LabeledCographTree.leaves] using hx
    subst x
    exact branchCell_root_adj ((hleaves h hh y).mp hy)
  · apply List.pairwise_map.mpr
    apply (hdisjoint.and hcross).imp_of_mem
    intro x y hx hy h a ha b hb
    exact (hG.branchCell_cross hM (hheads x hx) (hheads y hy) h.1
      ((hleaves x hx a).mp ha) ((hleaves y hy b).mp hb)).trans h.2

lemma assembleCograph_leaves (r : V) (s : Bool) (as bs : List V)
    (child : (V ⊕ V) → LabeledCographTree V) :
    (assembleCograph r s as bs child).leaves = r::(weave s as bs).flatMap (fun h => (child h).leaves) := by
  simp [assembleCograph,LabeledCographTree.attach_leaves,LabeledCographTree.leaves,List.flatMap_map]

lemma assembleCograph_nodup {M : Set V} (r : V) (s : Bool) (as bs : List V)
    (child : (V ⊕ V) → LabeledCographTree V)
    (hn : ∀h∈weave s as bs, (child h).leaves.Nodup)
    (hleaves : ∀h∈weave s as bs, ∀v, v∈(child h).leaves ↔ v∈branchCell G M r h)
    (hd : (weave s as bs).Pairwise (fun x y => Disjoint (branchCell G M r x) (branchCell G M r y))) :
    (assembleCograph r s as bs child).leaves.Nodup := by
  rw [assembleCograph_leaves]
  apply List.nodup_cons.mpr
  constructor
  · intro hr
    obtain ⟨h,hh,hr⟩ := List.mem_flatMap.mp hr
    exact branchCell_root_out M r h ((hleaves h hh r).mp hr)
  · apply List.nodup_flatMap.mpr
    refine ⟨hn,?_⟩
    apply hd.imp_of_mem
    intro x y hx hy hxy
    apply List.disjoint_left.mpr
    intro v hvx hvy
    exact Set.disjoint_left.mp hxy ((hleaves x hx v).mp hvx) ((hleaves y hy v).mp hvy)

/-- Covering the two literal profile-class families covers every original module
vertex exactly once, with the pivot left as the initial cotree leaf. -/
theorem assembleCograph_covers {M : Set V} {r : V} (hr : r∈M) (s : Bool) (as bs : List V)
    (child : (V ⊕ V) → LabeledCographTree V)
    (hleaves : ∀h∈weave s as bs, ∀v, v∈(child h).leaves ↔ v∈branchCell G M r h)
    (hcoverA : ∀v∈M, v∈nonneighbors G r → ∃a∈as, pivotProfile G r v = pivotProfile G r a)
    (hcoverB : ∀v∈M, G.Adj r v → ∃b∈bs, pivotProfile Gᶜ r v = pivotProfile Gᶜ r b) :
    ∀v, v∈(assembleCograph r s as bs child).leaves ↔ v∈M := by
  intro v
  rw [assembleCograph_leaves,List.mem_cons]
  constructor
  · rintro (rfl | hv)
    · exact hr
    · obtain ⟨h,hh,hv⟩ := List.mem_flatMap.mp hv
      have hm := (hleaves h hh v).mp hv
      cases h <;> exact hm.1
  · intro hv
    by_cases he : v=r
    · exact Or.inl he
    · right
      by_cases ha : G.Adj r v
      · obtain ⟨b,hb,hp⟩ := hcoverB v hv ha
        have hmem : Sum.inr b∈weave s as bs := (mem_weave s as bs _).mpr (Or.inr ⟨b,hb,rfl⟩)
        apply List.mem_flatMap.mpr
        refine ⟨Sum.inr b,hmem,(hleaves _ hmem v).mpr ?_⟩
        exact ⟨hv,by simpa only [nonneighbors_compl,mem_neighborSet] using ha,hp⟩
      · have hn : v∈nonneighbors G r := ⟨he,ha⟩
        obtain ⟨a,ha,hp⟩ := hcoverA v hv hn
        have hmem : Sum.inl a∈weave s as bs := (mem_weave s as bs _).mpr (Or.inl ⟨a,ha,rfl⟩)
        exact List.mem_flatMap.mpr ⟨Sum.inl a,hmem,(hleaves _ hmem v).mpr ⟨hv,hn,hp⟩⟩

end HiddenCircuits.DH
