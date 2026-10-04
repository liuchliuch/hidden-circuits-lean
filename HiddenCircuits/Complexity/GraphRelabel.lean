import HiddenCircuits.Complexity.GraphEncoding

/-! Executable graph relabeling into the canonical adjacency-matrix input format. -/
namespace HiddenCircuits.Complexity.MatrixGraph
variable {V : Type*} {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (e : V ≃ Fin n)

/-- Relabel an explicitly decidable graph, preserving every adjacency exactly. -/
def relabel : MatrixGraph n where
  edge i j := decide (G.Adj (e.symm i) (e.symm j))
  symm i j := by simp only [G.adj_comm]
  loopless i := by simp

@[simp] theorem relabel_adj (i j : Fin n) :
    (relabel G e).graph.Adj i j ↔ G.Adj (e.symm i) (e.symm j) := by
  change decide (G.Adj (e.symm i) (e.symm j)) = true ↔ _
  simp

/-- Independent vertex sets are preserved bijectively by the actual encoding graph. -/
def relabelIndependentEquiv :
    {s : Set V // G.IsIndepSet s} ≃ (relabel G e).IndependentSet where
  toFun s := ⟨{i | e.symm i ∈ s.val}, by
    intro i hi j hj hne hadj
    exact s.property hi hj (fun he => hne (e.symm.injective he)) ((relabel_adj G e i j).mp hadj)⟩
  invFun s := ⟨{v | e v ∈ s.val}, by
    intro v hv w hw hne hadj
    apply s.property hv hw (fun he => hne (e.injective he))
    apply (relabel_adj G e (e v) (e w)).mpr
    simpa using hadj⟩
  left_inv s := by
    apply Subtype.ext
    ext v
    simp
  right_inv s := by
    apply Subtype.ext
    ext i
    simp

end HiddenCircuits.Complexity.MatrixGraph
