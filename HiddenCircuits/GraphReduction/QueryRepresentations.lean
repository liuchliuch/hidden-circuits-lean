import HiddenCircuits.GraphReduction.QueryEncoding
import HiddenCircuits.GraphReduction.ExplicitProbeOrder

/-! Explicit representations on the actual Fin-labeled binary query graphs. -/
namespace HiddenCircuits.GraphReduction

namespace Enumeration
variable {V : Type*}

def embedding (a : Enumeration V) : Fin a.labels.length ↪ V :=
  ⟨a.labels.get,a.nodup.injective_get⟩

/-- Pulling endpoint coordinates along the actual label list is executable. -/
def diagram (a : Enumeration V) (D : PermutationDiagram V) : PermutationDiagram (Fin a.labels.length) :=
  D.restrict a.embedding

 theorem diagram_graph (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : PermutationDiagram V) (hD : D.graph=G) : (a.diagram D).graph=(a.matrixGraph G).graph := by
  ext i j
  change D.graph.Adj (a.labels.get i) (a.labels.get j) ↔ decide (G.Adj (a.labels.get i) (a.labels.get j))=true
  rw [hD]
  simp

/-- The graph-matrix emitter also carries the concrete common-length interval coordinates. -/
def intervalRepresentation (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : UnitInterval.Representation G) : UnitInterval.Representation (a.matrixGraph G).graph where
  length := r.length
  positive := r.positive
  left i := r.left (a.labels.get i)
  adjacency := by
    intro i j
    change decide (G.Adj (a.labels.get i) (a.labels.get j))=true ↔ _
    rw [decide_eq_true_eq,r.adjacency]
    have he : a.labels.get i≠a.labels.get j ↔ i≠j := a.nodup.injective_get.ne_iff
    rw [he]

/-- The actual elimination positions are transferred to the matrix's concrete numeric labels. -/
def eliminationOrder (a : Enumeration V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : PerfectEliminationOrder G) : PerfectEliminationOrder (a.matrixGraph G).graph where
  position i := o.position (a.labels.get i)
  injective := o.injective.comp a.nodup.injective_get
  later_clique := by
    intro x y z hxy hxz hpq hpr hyz
    change decide (G.Adj (a.labels.get x) (a.labels.get y))=true at hxy
    change decide (G.Adj (a.labels.get x) (a.labels.get z))=true at hxz
    change decide (G.Adj (a.labels.get y) (a.labels.get z))=true
    exact decide_eq_true_eq.mpr (o.later_clique _ _ _ (of_decide_eq_true hxy)
      (of_decide_eq_true hxz) hpq hpr (a.nodup.injective_get.ne hyz))

end Enumeration

/-- Compression now runs on Fin labels, with their executable finite enumeration. -/
def monotoneMatrixDiagram {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    PermutationDiagram (Fin (monotoneGraphInput pairs S T s).1) :=
  ((monotoneEnumeration S T s).diagram (retainedMonotoneDiagram pairs S T s)).compress

 theorem monotoneMatrixDiagram_graph {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    (monotoneMatrixDiagram pairs S T s).graph=(monotoneGraphInput pairs S T s).2.graph := by
  rw [monotoneMatrixDiagram,PermutationDiagram.compress_graph]
  exact Enumeration.diagram_graph _ _ _ (retainedMonotoneDiagram_graph pairs S T s)

 def privateMatrixDiagram {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    PermutationDiagram (Fin (privateGraphInput pairs S T s).1) :=
  ((privateEnumeration S T s).diagram (PrivateProbe.retainedDiagram pairs S T s)).compress

 theorem privateMatrixDiagram_graph {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    (privateMatrixDiagram pairs S T s).graph=(privateGraphInput pairs S T s).2.graph := by
  rw [privateMatrixDiagram,PermutationDiagram.compress_graph]
  exact Enumeration.diagram_graph _ _ _ (PrivateProbe.retainedDiagram_graph pairs S T s)

/-- The actual output endpoint ranks are below the number of vertices, on both lines. -/
theorem privateMatrixDiagram_bounds {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) (v : Fin (privateGraphInput pairs S T s).1) :
    (privateMatrixDiagram pairs S T s).upper v < (privateGraphInput pairs S T s).1 ∧
      (privateMatrixDiagram pairs S T s).lower v < (privateGraphInput pairs S T s).1 := by
  exact ⟨by simpa only [Fintype.card_fin] using PermutationDiagram.compress_upper_lt _ v,
    by simpa only [Fintype.card_fin] using PermutationDiagram.compress_lower_lt _ v⟩

 def unitMatrixRepresentation {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    UnitInterval.Representation (unitGraphInput (fun r => w.get r) S T s).2.graph :=
  (unitEnumeration S T s).intervalRepresentation _ (unitIntervalQueryUnitRepresentation w S T s)

@[simp] theorem unitMatrixRepresentation_length {p : ℕ} (w : List (CutPair p))
    (S T : State (2*p) p) (s : ℕ) : (unitMatrixRepresentation w S T s).length=1 := rfl

def privateMatrixEliminationOrder {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) : PerfectEliminationOrder (privateGraphInput pairs S T s).2.graph :=
  (privateEnumeration S T s).eliminationOrder _ (PrivateProbe.explicitRetainedQueryOrder pairs S T s)

 theorem privateGraphInput_chordal {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) : Chordal (privateGraphInput pairs S T s).2.graph :=
  (privateMatrixEliminationOrder pairs S T s).chordal

end HiddenCircuits.GraphReduction
