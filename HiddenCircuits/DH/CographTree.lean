import HiddenCircuits.DH.Cographs
import HiddenCircuits.DH.Decomposition

/-! Proof-side binary cotrees for ordinary P4-free graphs. This existence theorem
is an induction principle, not an asserted linear-time cotree constructor. -/
namespace HiddenCircuits.DH
open SimpleGraph

/-- Every internal node independently specifies disjoint union or complete join. -/
inductive CographTree where
  | leaf
  | node (joined : Bool) (left right : CographTree)
  deriving DecidableEq, Repr

namespace CographTree

def Vertex : CographTree → Type
  | .leaf => Unit
  | .node _ l r => l.Vertex ⊕ r.Vertex

instance vertexFintype : (t : CographTree) → Fintype t.Vertex
  | .leaf => inferInstanceAs (Fintype Unit)
  | .node _ l r => @instFintypeSum _ _ (vertexFintype l) (vertexFintype r)

instance vertexNonempty : (t : CographTree) → Nonempty t.Vertex
  | .leaf => ⟨()⟩
  | .node _ l _ => ⟨Sum.inl (Classical.choice (vertexNonempty l))⟩

def leaves : CographTree → ℕ
  | .leaf => 1
  | .node _ l r => l.leaves+r.leaves

def nodes : CographTree → ℕ
  | .leaf => 1
  | .node _ l r => l.nodes+r.nodes+1

@[simp] lemma card_vertex (t : CographTree) : Fintype.card t.Vertex = t.leaves := by
  induction t with
  | leaf => rfl
  | node b l r hl hr =>
    change Fintype.card (l.Vertex ⊕ r.Vertex) = l.leaves+r.leaves
    rw [Fintype.card_sum,hl,hr]

lemma nodes_eq (t : CographTree) : t.nodes+1 = 2*t.leaves := by
  induction t <;> simp [nodes,leaves, *] <;> omega

def mergeGraph {V W : Type*} (joined : Bool) (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) :=
  if joined then joinGraph G H Set.univ Set.univ else disjointGraph G H

def graph : (t : CographTree) → SimpleGraph t.Vertex
  | .leaf => ⊥
  | .node b l r => mergeGraph b l.graph r.graph

/-- The cotree is also an ordinary executable all-active bag expression. -/
def toBagExpr : CographTree → BagExpr
  | .leaf => .leaf
  | .node false l r => .falseTwin l.toBagExpr r.toBagExpr
  | .node true l r => .trueTwin l.toBagExpr r.toBagExpr

@[simp] lemma toBagExpr_active (t : CographTree) : t.toBagExpr.active = Set.univ := by
  induction t with
  | leaf => rfl
  | node b l r hl hr =>
    cases b <;> ext x <;> cases x <;> simp [toBagExpr,BagExpr.active,hl,hr,Set.mem_univ] <;> trivial

/-- Isomorphisms of children preserve either union or complete-join semantics. -/
def mergeCongr {V W V' W' : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {G' : SimpleGraph V'} {H' : SimpleGraph W'} (b : Bool) (e : G ≃g G') (f : H ≃g H') :
    mergeGraph b G H ≃g mergeGraph b G' H' where
  toEquiv := e.toEquiv.sumCongr f.toEquiv
  map_rel_iff' := by
    cases b <;> rintro (a | a) (c | c)
    · exact e.map_rel_iff
    · rfl
    · rfl
    · exact f.map_rel_iff
    · exact e.map_rel_iff
    · rfl
    · rfl
    · exact f.map_rel_iff

noncomputable def bagIso : (t : CographTree) → t.toBagExpr.graph ≃g t.graph
  | .leaf => Iso.refl
  | .node false l r => disjointCongrIso (bagIso l) (bagIso r)
  | .node true l r => by
      change joinGraph l.toBagExpr.graph r.toBagExpr.graph l.toBagExpr.active r.toBagExpr.active ≃g _
      rw [toBagExpr_active,toBagExpr_active]
      exact mergeCongr true (bagIso l) (bagIso r)

/-- A singleton graph is exactly a cotree leaf. -/
noncomputable def leafIso {V : Type*} [Nonempty V] [Subsingleton V] (G : SimpleGraph V) :
    CographTree.leaf.graph ≃g G where
  toEquiv := {
    toFun := fun _ => Classical.choice (inferInstance : Nonempty V)
    invFun := fun _ => ()
    left_inv := by intro x; cases x; rfl
    right_inv := by intro x; exact Subsingleton.elim _ _ }
  map_rel_iff' := by
    intro a b
    change G.Adj _ _ ↔ False
    exact iff_false_intro (fun h => h.ne (Subsingleton.elim _ _))

/-- Two complementary nonempty modules have a uniform complete or empty cut. -/
lemma complementary_modules_cut {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hS : GraphModule G S) (hT : GraphModule G Sᶜ) (a : S) (b : ↥(Sᶜ)) :
    ∀ x : S, ∀ y : ↥(Sᶜ), (G.Adj x.val y.val ↔ G.Adj a.val b.val) := by
  intro x y
  have hx := hS x.val x.property a.val a.property y.val y.property
  have hy := hT y.val y.property b.val b.property a.val (by simpa using a.property)
  exact hx.trans (by simpa only [G.adj_comm] using hy)

/-- Exact graph reconstruction across a complementary module split. -/
noncomputable def splitIso {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {S : Set V}
    (hS : GraphModule G S) (hT : GraphModule G Sᶜ) (a : S) (b : ↥(Sᶜ)) :
    mergeGraph (decide (G.Adj a.val b.val)) (G.induce S) (G.induce Sᶜ) ≃g G := by
  classical
  refine { toEquiv := Equiv.sumCompl (fun v => v ∈ S), map_rel_iff' := ?_ }
  rintro (x | x) (y | y)
  · cases h : decide (G.Adj a.val b.val) <;> rfl
  · change G.Adj x.val y.val ↔ _
    have hxy := complementary_modules_cut hS hT a b x y
    by_cases hab : G.Adj a.val b.val <;> simp [mergeGraph,hab,joinGraph,disjointGraph] <;> tauto
  · change G.Adj x.val y.val ↔ _
    have hxy := complementary_modules_cut hS hT a b y x
    have hyx : G.Adj x.val y.val ↔ G.Adj a.val b.val := by simpa only [G.adj_comm] using hxy
    by_cases hab : G.Adj a.val b.val <;> simp [mergeGraph,hab,joinGraph,disjointGraph] <;> tauto
  · cases h : decide (G.Adj a.val b.val) <;> rfl

universe u

private theorem exists_tree_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      Fintype.card V = n → P4Free G → ∃ t : CographTree, Nonempty (t.graph ≃g G) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G hn hG
    by_cases hs : Subsingleton V
    · letI := hs
      exact ⟨.leaf,⟨leafIso G⟩⟩
    · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hs
      obtain ⟨S,hS,hT,hmS,hmT⟩ := hG.module_split
      obtain ⟨a,ha⟩ := hS
      obtain ⟨b,hb⟩ := hT
      letI : Nonempty S := ⟨⟨a,ha⟩⟩
      letI : Nonempty ↥(Sᶜ) := ⟨⟨b,hb⟩⟩
      have hSl : Fintype.card S < n := by rw [← hn]; exact Fintype.card_subtype_lt hb
      have hTl : Fintype.card ↥(Sᶜ) < n := by
        rw [← hn]
        apply Fintype.card_subtype_lt (x := a)
        simpa using ha
      obtain ⟨l,⟨el⟩⟩ := ih (Fintype.card S) hSl S (G.induce S) rfl (hG.induce S)
      obtain ⟨r,⟨er⟩⟩ := ih (Fintype.card ↥(Sᶜ)) hTl ↥(Sᶜ) (G.induce Sᶜ) rfl (hG.induce Sᶜ)
      let joined := decide (G.Adj a b)
      refine ⟨.node joined l r,⟨?_⟩⟩
      exact (mergeCongr joined el er).trans (splitIso hmS hmT ⟨a,ha⟩ ⟨b,hb⟩)

/-- Every ordinary finite nonempty P4-free graph has a graph-isomorphic binary
cotree, derived from the semantic no-induced-P4 condition. -/
theorem exists_of_p4Free {V : Type*} [Finite V] [Nonempty V] {G : SimpleGraph V} (hG : P4Free G) :
    ∃ t : CographTree, Nonempty (t.graph ≃g G) := by
  classical
  letI := Fintype.ofFinite V
  exact exists_tree_card (Fintype.card V) V G rfl hG

end CographTree
end HiddenCircuits.DH
