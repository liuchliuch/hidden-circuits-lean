import HiddenCircuits.DH.CographExtraction

/-! Substitute already-computed graph bags into an actual labeled cotree.
Leaf evaluation reuses an existing expression; only cotree internal nodes are allocated. -/
namespace HiddenCircuits.DH
universe u v
namespace LabeledCographTree
variable {R : Type v}

def substitute (bags : R → BagExpr) : LabeledCographTree R → BagExpr
  | .leaf r => bags r
  | .node false l r => .falseTwin (l.substitute bags) (r.substitute bags)
  | .node true l r => .trueTwin (l.substitute bags) (r.substitute bags)

/-- Every vertex of a substituted bag still belongs to one literal cotree leaf. -/
def leafIndex (bags : R → BagExpr) : (t : LabeledCographTree R) →
    (t.substitute bags).Vertex → t.shape.Vertex
  | .leaf _,_ => ()
  | .node false l _,.inl x => .inl (l.leafIndex bags x)
  | .node false _ r,.inr y => .inr (r.leafIndex bags y)
  | .node true l _,.inl x => .inl (l.leafIndex bags x)
  | .node true _ r,.inr y => .inr (r.leafIndex bags y)

lemma substitute_size (bags : R → BagExpr) (t : LabeledCographTree R) :
    (t.substitute bags).size = (t.leaves.map (fun r => (bags r).size)).sum := by
  induction t with
  | leaf r => simp [substitute,leaves]
  | node b l r hl hr => cases b <;> simp [substitute,BagExpr.size,leaves,hl,hr]

/-- Relabel cotree leaves while preserving the executable merge shape. -/
def mapLabels {Q : Type*} (f : R → Q) : LabeledCographTree R → LabeledCographTree Q
  | .leaf r => .leaf (f r)
  | .node b l r => .node b (l.mapLabels f) (r.mapLabels f)

@[simp] lemma mapLabels_leaves {Q : Type*} (f : R → Q) (t : LabeledCographTree R) :
    (t.mapLabels f).leaves = t.leaves.map f := by
  induction t <;> simp [mapLabels,leaves, *]

lemma mapLabels_substitute {Q : Type*} (f : R → Q) (bags : Q → BagExpr) (t : LabeledCographTree R) :
    (t.mapLabels f).substitute bags = t.substitute (fun r => bags (f r)) := by
  induction t with
  | leaf r => rfl
  | node b l r hl hr => cases b <;> simp [mapLabels,substitute,hl,hr]

lemma substitute_congr (bags bags' : R → BagExpr) (t : LabeledCographTree R)
    (h : ∀ r ∈ t.leaves, bags r=bags' r) : t.substitute bags = t.substitute bags' := by
  induction t with
  | leaf r => exact h r List.mem_cons_self
  | node b l r hl hr =>
    have hleft := hl (fun v hv => h v (List.mem_append_left _ hv))
    have hright := hr (fun v hv => h v (List.mem_append_right _ hv))
    cases b <;> simp [substitute,hleft,hright]

lemma Correct.left {K : SimpleGraph R} {b : Bool} {l r : LabeledCographTree R}
    (h : Correct K (.node b l r)) : Correct K l := by
  intro a a'
  have h := h (Sum.inl a) (Sum.inl a')
  cases b <;> exact h

lemma Correct.right {K : SimpleGraph R} {b : Bool} {l r : LabeledCographTree R}
    (h : Correct K (.node b l r)) : Correct K r := by
  intro a a'
  have h := h (Sum.inr a) (Sum.inr a')
  cases b <;> exact h

lemma Correct.cross_iff {K : SimpleGraph R} {b : Bool} {l r : LabeledCographTree R}
    (h : Correct K (.node b l r)) {u v : R} (hu : u∈l.leaves) (hv : v∈r.leaves) :
    K.Adj u v ↔ b=true := by
  obtain ⟨x,rfl⟩ := (l.mem_leaves_iff u).mp hu
  obtain ⟨y,rfl⟩ := (r.mem_leaves_iff v).mp hv
  have hc := h (Sum.inl x) (Sum.inr y)
  cases b <;> simpa [label,shape,CographTree.graph,CographTree.mergeGraph,joinGraph,disjointGraph] using hc

lemma Correct.mapLabels {Q : Type*} {K : SimpleGraph R} {K' : SimpleGraph Q}
    (f : R → Q) (t : LabeledCographTree R) (ht : Correct K t)
    (hf : ∀ u∈t.leaves, ∀ v∈t.leaves, K'.Adj (f u) (f v) ↔ K.Adj u v) :
    Correct K' (t.mapLabels f) := by
  induction t with
  | leaf r => exact correct_leaf _ _
  | node b l r hl hr =>
    apply Correct.node b
    · exact hl ht.left (fun u hu v hv => hf u (List.mem_append_left _ hu) v (List.mem_append_left _ hv))
    · exact hr ht.right (fun u hu v hv => hf u (List.mem_append_right _ hu) v (List.mem_append_right _ hv))
    · intro x hx y hy
      rw [mapLabels_leaves] at hx hy
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
      exact (hf u (List.mem_append_left _ hu) v (List.mem_append_right _ hv)).trans (ht.cross_iff hu hv)

@[simp] lemma mapLabels_shape {Q : Type*} (f : R → Q) (t : LabeledCographTree R) :
    (t.mapLabels f).shape = t.shape := by
  induction t <;> simp [mapLabels,shape, *]

@[simp] lemma shape_leaves (t : LabeledCographTree R) : t.shape.leaves=t.leaves.length := by
  induction t <;> simp [shape,leaves,CographTree.leaves, *]

end LabeledCographTree

namespace BoundaryPartition
variable {V : Type u} {R : Type v} {G : SimpleGraph V} {H : SimpleGraph R}
variable (p : BoundaryPartition G H) (rep : p.Representation)

/-- Actual original vertices represented by the recursively substituted bag. -/
def realize : (t : LabeledCographTree R) → (t.substitute rep.expr).Vertex → V
  | .leaf r,x => (rep.iso r x).val
  | .node false l _,.inl x => realize l x
  | .node false _ r,.inr y => realize r y
  | .node true l _,.inl x => realize l x
  | .node true _ r,.inr y => realize r y

lemma realize_place (t : LabeledCographTree R) (x : (t.substitute rep.expr).Vertex) :
    p.place (p.realize rep t x) = t.label (t.leafIndex rep.expr x) := by
  induction t with
  | leaf r => exact (rep.iso r x).property
  | node b l r hl hr => cases b <;> cases x <;> first | exact hl _ | exact hr _

lemma realize_active (t : LabeledCographTree R) (x : (t.substitute rep.expr).Vertex) :
    p.realize rep t x ∈ p.active ↔ x ∈ (t.substitute rep.expr).active := by
  induction t with
  | leaf r =>
    have hi := iso_mem_image (rep.iso r) (rep.expr r).active x
    rw [rep.active_image] at hi
    exact hi
  | node b l r hl hr => cases b <;> cases x <;> first | exact hl _ | exact hr _

lemma realize_injective (t : LabeledCographTree R) (hn : t.leaves.Nodup) :
    Function.Injective (p.realize rep t) := by
  induction t with
  | leaf r =>
    intro x y he
    exact (rep.iso r).injective (Subtype.ext he)
  | node b l r hl hr =>
    obtain ⟨hnl,hnr,hcross⟩ := List.nodup_append.mp hn
    cases b <;> intro x y he <;> cases x <;> cases y
    all_goals first
    | exact congrArg Sum.inl (hl hnl he)
    | exact congrArg Sum.inr (hr hnr he)
    | exact False.elim (hcross _ (l.mem_leaves_label _) _ (r.mem_leaves_label _)
        ((p.realize_place rep l _).symm.trans ((congrArg p.place he).trans (p.realize_place rep r _))))
    | exact False.elim (hcross _ (l.mem_leaves_label _) _ (r.mem_leaves_label _)
        ((p.realize_place rep l _).symm.trans ((congrArg p.place he.symm).trans (p.realize_place rep r _))))

lemma realize_surjective (t : LabeledCographTree R) {a : V} (ha : p.place a ∈ t.leaves) :
    ∃ x, p.realize rep t x = a := by
  induction t with
  | leaf r =>
    have har : p.place a=r := by simpa [LabeledCographTree.leaves] using ha
    obtain ⟨x,hx⟩ := (rep.iso r).toEquiv.surjective ⟨a,har⟩
    exact ⟨x,congrArg Subtype.val hx⟩
  | node b l r hl hr =>
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨x,hx⟩ := hl ha
      cases b <;> exact ⟨Sum.inl x,hx⟩
    · obtain ⟨y,hy⟩ := hr ha
      cases b <;> exact ⟨Sum.inr y,hy⟩

/-- A cotree's genuine complete/empty cuts lift through every existing active bag boundary. -/
theorem realize_adj (t : LabeledCographTree R) (hn : t.leaves.Nodup) (hc : t.Correct H)
    (x y : (t.substitute rep.expr).Vertex) :
    G.Adj (p.realize rep t x) (p.realize rep t y) ↔ (t.substitute rep.expr).graph.Adj x y := by
  induction t with
  | leaf r => exact (rep.iso r).map_rel_iff
  | node b l r hl hr =>
    obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.mp hn
    have hcl : l.Correct H := by
      intro a b'
      have h := hc (Sum.inl a) (Sum.inl b')
      cases b <;> exact h
    have hcr : r.Correct H := by
      intro a b'
      have h := hc (Sum.inr a) (Sum.inr b')
      cases b <;> exact h
    have cross (a : (l.substitute rep.expr).Vertex) (b' : (r.substitute rep.expr).Vertex) :
        G.Adj (p.realize rep l a) (p.realize rep r b') ↔
          a ∈ (l.substitute rep.expr).active ∧ b' ∈ (r.substitute rep.expr).active ∧ b=true := by
      have hne : p.place (p.realize rep l a) ≠ p.place (p.realize rep r b') := by
        rw [p.realize_place,p.realize_place]
        exact hdis _ (l.mem_leaves_label _) _ (r.mem_leaves_label _)
      have hadj := hc (Sum.inl (l.leafIndex rep.expr a)) (Sum.inr (r.leafIndex rep.expr b'))
      have he : H.Adj (p.place (p.realize rep l a)) (p.place (p.realize rep r b')) ↔ b=true := by
        rw [p.realize_place,p.realize_place]
        cases b <;> simpa [LabeledCographTree.shape,LabeledCographTree.label,CographTree.graph,
          CographTree.mergeGraph,disjointGraph,joinGraph] using hadj
      rw [p.block _ _ hne,p.realize_active,p.realize_active,he]
    cases b <;> cases x <;> cases y
    all_goals first
    | exact hl hnl hcl _ _
    | exact hr hnr hcr _ _
    | simpa [LabeledCographTree.substitute,BagExpr.graph,disjointGraph,joinGraph] using cross _ _
    | simpa [LabeledCographTree.substitute,BagExpr.graph,disjointGraph,joinGraph,G.adj_comm,and_comm] using cross _ _

/-- The original-vertex region represented by all leaves of a labeled cotree. -/
def region (t : LabeledCographTree R) : Set V := {a | p.place a ∈ t.leaves}

noncomputable def substituteIso (t : LabeledCographTree R) (hn : t.leaves.Nodup) (hc : t.Correct H) :
    (t.substitute rep.expr).graph ≃g G.induce (p.region t) := by
  let f : (t.substitute rep.expr).Vertex → p.region t := fun x =>
    ⟨p.realize rep t x,by change p.place (p.realize rep t x) ∈ t.leaves; rw [p.realize_place]; exact t.mem_leaves_label _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact p.realize_injective rep t hn (congrArg Subtype.val he)
    · intro a
      obtain ⟨x,hx⟩ := p.realize_surjective rep t a.property
      exact ⟨x,Subtype.ext hx⟩
  exact
    { toEquiv := Equiv.ofBijective f hf
      map_rel_iff' := by intro x y; exact p.realize_adj rep t hn hc x y }

lemma substituteIso_active (t : LabeledCographTree R) (hn : t.leaves.Nodup) (hc : t.Correct H) :
    p.substituteIso rep t hn hc '' (t.substitute rep.expr).active =
      {a : p.region t | a.val ∈ p.active} := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (p.realize_active rep t x).mpr hx
  · intro ha
    obtain ⟨x,rfl⟩ := (p.substituteIso rep t hn hc).toEquiv.surjective a
    exact ⟨x,(p.realize_active rep t x).mp ha,rfl⟩

end BoundaryPartition
end HiddenCircuits.DH
