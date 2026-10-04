import HiddenCircuits.GraphReduction.MonotonePermutation
import HiddenCircuits.GraphReduction.Runtime.MonotoneHardness
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Natural ordered graph classes and the whole-class monotone/permutation theorem.
All predicates concern the actual input graph up to isomorphism. Convexity is the
usual consecutive-neighbor condition, independently of endpoint monotonicity. -/
namespace HiddenCircuits.GraphReduction

/-- A genuine two-line permutation representation of the same labeled graph. -/
def PermutationGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ D : PermutationDiagram V, D.graph = G

/-- The intersection of the ordinary bipartite and permutation graph classes. -/
def BipartitePermutationGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsBipartite ∧ PermutationGraph G

lemma PermutationGraph.of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (h : PermutationGraph H) : PermutationGraph G := by
  obtain ⟨D,hD⟩ := h
  refine ⟨D.restrict e.toEquiv.toEmbedding,?_⟩
  ext x y
  change D.graph.Adj (e x) (e y) ↔ G.Adj x y
  rw [hD]
  exact e.map_adj_iff

lemma cutGraph_isBipartite {X Y : Type*} (R : X → Y → Prop) : (cutGraph R).IsBipartite := by
  refine ⟨{ toFun := fun v => Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) v
            map_rel' := ?_ }⟩
  intro v w h
  cases v <;> cases w <;> simp_all [cutGraph]

/-- A proper two-coloring gives a label-preserving isomorphism onto its actual cut. -/
noncomputable def coloringCutIso {V : Type} {G : SimpleGraph V}
    (c : G.Coloring (Fin 2)) :
    cutGraph (fun (x : {v // c v = 0}) (y : {v // c v ≠ 0}) => G.Adj x.val y.val) ≃g G := by
  classical
  refine { toEquiv := Equiv.sumCompl (fun v => c v = 0), map_rel_iff' := ?_ }
  intro a b
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      change G.Adj x.val y.val ↔ False
      refine iff_false_intro (fun h => ?_)
      have hn := c.valid h
      exact hn (x.property.trans y.property.symm)
    | inr y => rfl
  | inr x =>
    cases b with
    | inl y => exact G.adj_comm _ _
    | inr y =>
      change G.Adj x.val y.val ↔ False
      refine iff_false_intro (fun h => ?_)
      have hn := c.valid h
      have hx := x.property
      have hy := y.property
      have hb₁ := (c x.val).isLt
      have hb₂ := (c y.val).isLt
      apply hn
      apply Fin.ext
      have hx0 : (c x.val).val ≠ 0 := fun he => hx (Fin.ext he)
      have hy0 : (c y.val).val ≠ 0 := fun he => hy (Fin.ext he)
      omega

/-- Every finite monotone graph has an actual permutation diagram, including isolates. -/
theorem MonotoneGraph.bipartitePermutation {V : Type} {G : SimpleGraph V}
    (hG : MonotoneGraph G) : BipartitePermutationGraph G := by
  obtain ⟨X,Y,hX,hY,R,⟨o⟩,⟨e⟩⟩ := hG
  exact ⟨SimpleGraph.Colorable.of_hom e.toHom (cutGraph_isBipartite R),
    PermutationGraph.of_iso e ⟨o.permutationDiagram,o.permutationDiagram_graph⟩⟩

/-- Sorting the two independent endpoint lists reconstructs a monotone ordering. -/
theorem BipartitePermutationGraph.monotone {V : Type} [Finite V] {G : SimpleGraph V}
    (hG : BipartitePermutationGraph G) : MonotoneGraph G := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨⟨c⟩,D,hD⟩ := hG
  let X := {v // c v = 0}
  let Y := {v // c v ≠ 0}
  let e := coloringCutIso c
  let E := D.restrict e.toEquiv.toEmbedding
  have hE : E.graph = cutGraph (fun (x : X) (y : Y) => G.Adj x.val y.val) := by
    ext x y
    change D.graph.Adj (e x) (e y) ↔ _
    rw [hD]
    exact e.map_adj_iff
  have hx : ∀ x x' : X, ¬E.graph.Adj (.inl x) (.inl x') := by
    intro x x'
    rw [hE]
    exact not_false
  have hy : ∀ y y' : Y, ¬E.graph.Adj (.inr y) (.inr y') := by
    intro y y'
    rw [hE]
    exact not_false
  refine ⟨X,Y,inferInstance,inferInstance,fun x y => G.Adj x.val y.val,?_,⟨e.symm⟩⟩
  have ho := E.monotoneOrdering hx hy
  rw [hE] at ho
  exact ⟨ho⟩

/-- Equation (2.4), for arbitrary finite labeled graphs with isolated vertices allowed. -/
theorem monotoneGraph_iff_bipartitePermutationGraph {V : Type} [Finite V]
    (G : SimpleGraph V) : MonotoneGraph G ↔ BipartitePermutationGraph G :=
  ⟨MonotoneGraph.bipartitePermutation,BipartitePermutationGraph.monotone⟩

/-- An ordering of one part in which each opposite neighborhood is consecutive. -/
structure ConvexOrdering {X Y : Type*} [Fintype Y] (R : X → Y → Prop) where
  columns : Fin (Fintype.card Y) ≃ Y
  consecutive : ∀ x i j k, i ≤ j → j ≤ k → R x (columns i) → R x (columns k) →
    R x (columns j)

/-- Both sides have the consecutive-neighbor property, in independently chosen orders. -/
structure BiconvexOrdering {X Y : Type*} [Fintype X] [Fintype Y] (R : X → Y → Prop) where
  rowConvex : ConvexOrdering R
  columnConvex : ConvexOrdering (fun y x => R x y)

/-- Ordinary convex bipartite graphs; witnesses are representation data, not oracle premises. -/
def ConvexGraph {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (X Y : Type) (_ : Fintype X) (_ : Fintype Y) (R : X → Y → Prop),
    Nonempty (ConvexOrdering R) ∧ Nonempty (G ≃g cutGraph R)

/-- Ordinary biconvex bipartite graphs. -/
def BiconvexGraph {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (X Y : Type) (_ : Fintype X) (_ : Fintype Y) (R : X → Y → Prop),
    Nonempty (BiconvexOrdering R) ∧ Nonempty (G ≃g cutGraph R)

namespace MonotoneOrdering
variable {X Y : Type*} [Fintype X] [Fintype Y] {R : X → Y → Prop}

/-- Row convexity is already present in the half-open endpoint description. -/
def rowConvexOrdering (o : MonotoneOrdering R) : ConvexOrdering R where
  columns := o.columns
  consecutive := by
    intro x i j k hij hjk hi hk
    have hi' := (o.neighborhood (o.rows.symm x) i).mp (by simpa using hi)
    have hk' := (o.neighborhood (o.rows.symm x) k).mp (by simpa using hk)
    have hj : R (o.rows (o.rows.symm x)) (o.columns j) :=
      (o.neighborhood _ _).mpr ⟨hi'.1.trans hij,lt_of_le_of_lt hjk hk'.2⟩
    simpa using hj

/-- Monotone endpoints force consecutive column neighborhoods too. -/
def columnConvexOrdering (o : MonotoneOrdering R) : ConvexOrdering (fun y x => R x y) where
  columns := o.rows
  consecutive := by
    intro y i j k hij hjk hi hk
    have hi' := (o.neighborhood i (o.columns.symm y)).mp (by simpa using hi)
    have hk' := (o.neighborhood k (o.columns.symm y)).mp (by simpa using hk)
    have hj : R (o.rows j) (o.columns (o.columns.symm y)) :=
      (o.neighborhood _ _).mpr ⟨(o.lo_mono hjk).trans hk'.1,hi'.2.trans_le (o.hi_mono hij)⟩
    simpa using hj

def biconvexOrdering (o : MonotoneOrdering R) : BiconvexOrdering R :=
  ⟨o.rowConvexOrdering,o.columnConvexOrdering⟩
end MonotoneOrdering

theorem MonotoneGraph.biconvex {V : Type} {G : SimpleGraph V} (hG : MonotoneGraph G) :
    BiconvexGraph G := by
  obtain ⟨X,Y,hX,hY,R,⟨o⟩,he⟩ := hG
  exact ⟨X,Y,hX,hY,R,⟨o.biconvexOrdering⟩,he⟩

theorem BiconvexGraph.convex {V : Type} {G : SimpleGraph V} (hG : BiconvexGraph G) :
    ConvexGraph G := by
  obtain ⟨X,Y,hX,hY,R,⟨o⟩,he⟩ := hG
  exact ⟨X,Y,hX,hY,R,⟨o.rowConvex⟩,he⟩

theorem MonotoneGraph.convex {V : Type} {G : SimpleGraph V} (hG : MonotoneGraph G) :
    ConvexGraph G := hG.biconvex.convex

end HiddenCircuits.GraphReduction
