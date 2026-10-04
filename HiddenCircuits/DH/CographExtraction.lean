import HiddenCircuits.DH.CographProfileOrder

/-! Executable labeled cotree assembly and graph-isomorphism extraction. -/
namespace HiddenCircuits.DH
open SimpleGraph

/-- Leaves retain actual input vertex labels; node tags are computed by the
profile-staircase extractor. -/
inductive LabeledCographTree (V : Type*) where
  | leaf (vertex : V)
  | node (joined : Bool) (left right : LabeledCographTree V)
  deriving Repr

namespace LabeledCographTree
variable {V : Type*}

def shape : LabeledCographTree V → CographTree
  | .leaf _ => .leaf
  | .node b l r => .node b l.shape r.shape

def label : (t : LabeledCographTree V) → t.shape.Vertex → V
  | .leaf v,_ => v
  | .node _ l _,.inl x => l.label x
  | .node _ _ r,.inr y => r.label y

def leaves : LabeledCographTree V → List V
  | .leaf v => [v]
  | .node _ l r => l.leaves++r.leaves

lemma mem_leaves_label (t : LabeledCographTree V) (x : t.shape.Vertex) : t.label x∈t.leaves := by
  induction t with
  | leaf v => simp [label,leaves]
  | node b l r hl hr =>
    cases x with
    | inl x => exact List.mem_append_left _ (hl x)
    | inr x => exact List.mem_append_right _ (hr x)

lemma mem_leaves_iff (t : LabeledCographTree V) (v : V) :
    v∈t.leaves ↔ ∃x:t.shape.Vertex, t.label x=v := by
  constructor
  · induction t with
    | leaf u => intro h; exact ⟨(),by simpa [leaves,label,eq_comm] using h⟩
    | node b l r hl hr =>
      intro h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨x,hx⟩ := hl h; exact ⟨Sum.inl x,hx⟩
      · obtain ⟨x,hx⟩ := hr h; exact ⟨Sum.inr x,hx⟩
  · rintro ⟨x,rfl⟩; exact t.mem_leaves_label x

lemma label_injective (t : LabeledCographTree V) (hn : t.leaves.Nodup) :
    Function.Injective t.label := by
  induction t with
  | leaf v => intro x y h; cases x; cases y; rfl
  | node b l r hl hr =>
    obtain ⟨hnl,hnr,hcross⟩ := List.nodup_append.mp hn
    intro x y he
    cases x <;> cases y
    · exact congrArg Sum.inl (hl hnl he)
    · exact False.elim (hcross _ (l.mem_leaves_label _) _ (r.mem_leaves_label _) he)
    · exact False.elim (hcross _ (l.mem_leaves_label _) _ (r.mem_leaves_label _) he.symm)
    · exact congrArg Sum.inr (hr hnr he)

/-- Exact represented adjacency; labels are ordinary original vertices. -/
def Correct (G : SimpleGraph V) (t : LabeledCographTree V) : Prop :=
  ∀x y:t.shape.Vertex, G.Adj (t.label x) (t.label y) ↔ t.shape.graph.Adj x y

lemma correct_leaf (G : SimpleGraph V) (v : V) : Correct G (.leaf v) := by
  intro x y
  simp [label,shape,CographTree.graph]

/-- Node assembly needs only the already established child semantics and the
literal complete/empty cross cut. -/
lemma Correct.node {G : SimpleGraph V} {l r : LabeledCographTree V} (b : Bool)
    (hl : Correct G l) (hr : Correct G r)
    (hcross : ∀x∈l.leaves, ∀y∈r.leaves, (G.Adj x y ↔ b=true)) :
    Correct G (.node b l r) := by
  rintro (x | x) (y | y)
  · cases b <;> exact hl x y
  · have h := hcross _ (l.mem_leaves_label x) _ (r.mem_leaves_label y)
    cases b <;> simpa [label,shape,CographTree.graph,CographTree.mergeGraph,joinGraph,disjointGraph] using h
  · have h := hcross _ (l.mem_leaves_label y) _ (r.mem_leaves_label x)
    cases b <;> simpa [label,shape,CographTree.graph,CographTree.mergeGraph,joinGraph,disjointGraph,G.adj_comm] using h
  · cases b <;> exact hr x y

/-- A correct duplicate-free labeled tree yields the actual induced-graph
isomorphism consumed by the verified bag evaluator. -/
noncomputable def inducedIso {G : SimpleGraph V} (t : LabeledCographTree V)
    (hn : t.leaves.Nodup) (hc : Correct G t) :
    t.shape.graph ≃g G.induce {v | v∈t.leaves} := by
  let f : t.shape.Vertex → {v | v∈t.leaves} := fun x => ⟨t.label x,t.mem_leaves_label x⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact t.label_injective hn (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,hx⟩ := (t.mem_leaves_iff y.val).mp y.property
      exact ⟨x,Subtype.ext hx⟩
  exact { toEquiv := Equiv.ofBijective f hf, map_rel_iff' := by intro a b; exact hc a b }

/-- Attach branch cotrees in the computed inner-to-outer order. -/
def attach : LabeledCographTree V → List (Bool × LabeledCographTree V) → LabeledCographTree V
  | t,[] => t
  | t,(b,u)::us => attach (.node b t u) us

lemma attach_leaves (t : LabeledCographTree V) (branches : List (Bool × LabeledCographTree V)) :
    (attach t branches).leaves = t.leaves++branches.flatMap (fun p => p.2.leaves) := by
  induction branches generalizing t with
  | nil => simp [attach]
  | cons p ps ih => rcases p with ⟨b,u⟩; simp [attach,ih,leaves,List.append_assoc]

/-- Local branch correctness and the staircase's later-tag rule assemble an
exact cotree for the entire ordered branch union. -/
theorem correct_attach {G : SimpleGraph V} (t : LabeledCographTree V)
    (branches : List (Bool × LabeledCographTree V)) (ht : Correct G t)
    (hc : ∀p∈branches, Correct G p.2)
    (hroot : ∀p∈branches, ∀x∈t.leaves, ∀y∈p.2.leaves, (G.Adj x y ↔ p.1=true))
    (hcross : branches.Pairwise (fun p q =>
      ∀x∈p.2.leaves, ∀y∈q.2.leaves, (G.Adj x y ↔ q.1=true))) :
    Correct G (attach t branches) := by
  induction branches generalizing t with
  | nil => exact ht
  | cons p ps ih =>
    rcases p with ⟨b,u⟩
    apply ih (.node b t u)
    · exact ht.node b (hc _ List.mem_cons_self) (hroot _ List.mem_cons_self)
    · intro p hp; exact hc p (List.mem_cons_of_mem _ hp)
    · intro p hp x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact hroot p (List.mem_cons_of_mem _ hp) x hx y hy
      · exact (List.pairwise_cons.mp hcross).1 p hp x hx y hy
    · exact (List.pairwise_cons.mp hcross).2

end LabeledCographTree
end HiddenCircuits.DH
