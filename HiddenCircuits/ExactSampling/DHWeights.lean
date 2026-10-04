import HiddenCircuits.DH.BinaryRuntime
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualMathematics
import HiddenCircuits.Approximation.SelfReduction.MatchingFibers
import HiddenCircuits.ExactSampling.Rejection

/-!
# Exact residual weights obtained from the checked DH binary program

All algorithmic count queries below invoke `DH.BinaryRuntime.function` on the
literal dense residual graph emitted by `GraphResidual.program`. Mathematical
perfect-matching cardinalities appear only in the correctness proofs.
-/
namespace HiddenCircuits.ExactSampling.DHWeights
open Complexity DH Approximation Approximation.SelfReduction
open Approximation.SelfReduction.Runtime
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Reachable distances are preserved by an induced embedding into a DH graph. -/
theorem embedding_distance {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : DistanceHereditaryGraph G) (f : H ↪g G) {a b : W} (hr : H.Reachable a b) :
    H.dist a b=G.dist (f a) (f b) := by
  let e := embeddingRangeIso f
  have hh := hG.induce_dist_of_reachable (hr.map e.toHom)
  exact (iso_dist_eq e a b).symm.trans hh

/-- Closure includes relabeling, not just literal subtype vertex deletion. -/
theorem hereditary_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : DistanceHereditaryGraph G) (f : H ↪g G) : DistanceHereditaryGraph H := by
  intro S hc a b
  let inc : H.induce S ↪g H := ⟨⟨Subtype.val,Subtype.val_injective⟩,by intro x y; rfl⟩
  have h₁ := hG.embedding_dist (f.comp inc) hc a b
  have h₂ := embedding_distance hG f ((hc a b).map inc.toHom)
  exact h₁.symm.trans h₂.symm

 theorem residual_hereditary {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (j : Fin (N+1)) :
    DistanceHereditaryGraph (GraphResidual.graph G j).graph := by
  let e := GraphResidual.graphIso G j
  let inc : G.graph.induce (withoutPair (0:Fin (N+1)) j) ↪g G.graph :=
    ⟨⟨Subtype.val,Subtype.val_injective⟩,by intro x y; rfl⟩
  exact hereditary_embedding hG (inc.comp e.toEmbedding)

/-- The actual deterministic binary count endpoint, decoded only for semantics. -/
def count (G : GraphInput) : ℕ := Computability.decodeNat (BinaryRuntime.function G.encode)

 theorem count_correct (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) :
    count G=perfectMatchingCount G.2.graph := by
  rw [count,BinaryRuntime.distanceHereditary G hG]
  exact Computability.decode_encodeNat _

/-- Every candidate is tested for being an actual edge before its residual
count is used. A forbidden edge has zero weight. -/
def weight {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) : ℕ :=
  if G.edge 0 j then count ⟨_,GraphResidual.graph G j⟩ else 0

 theorem weight_eq_fiber {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (j : Fin (N+1)) :
    weight G j=Fintype.card (EdgeFiber G.graph 0 j) := by
  by_cases ha : G.graph.Adj 0 j
  · have he : G.edge 0 j=true := ha
    simp only [weight,he,ite_true]
    rw [count_correct _ (residual_hereditary G hG j)]
    exact GraphResidual.graph_count_fiber G j ha
  · have he : G.edge 0 j=false := by
      apply Bool.eq_false_iff.mpr
      exact ha
    simp only [weight,he,Bool.false_eq_true,ite_false]
    symm
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun p => ha (by simpa [p.property] using p.val.property.2 0)⟩

 theorem weight_eq_child {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (j : Fin (N+1)) :
    weight G j=matchingChildCount G.graph 0 j := by
  rw [weight_eq_fiber G hG j,matchingChildCount_eq_fiber]
  simp only [Fintype.card_eq_nat_card]

 theorem count_eq_sum_weights {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) : count ⟨N+1,G⟩=∑j,weight G j := by
  rw [count_correct _ hG,matching_count_sum_all_partners G.graph (0:Fin (N+1))]
  exact Finset.sum_congr rfl (fun j _ => (weight_eq_child G hG j).symm)

/-- Deterministic weighted interval selection. `finSigmaFinEquiv` is recursively
implemented by ordered integer intervals, not an enumeration of matchings. -/
def splitIndex {N : ℕ} (G : MatrixGraph (N+1)) (hG : DistanceHereditaryGraph G.graph) :
    Fin (count ⟨N+1,G⟩) ≃ (Σj : Fin (N+1),Fin (weight G j)) :=
  (finCongr (count_eq_sum_weights G hG)).trans finSigmaFinEquiv.symm

/-- The physical interval represented by a selected branch and residual index. -/
 theorem splitIndex_interval {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) :
    x.val=(∑i : Fin (splitIndex G hG x).1,
      weight G (Fin.castLE (splitIndex G hG x).1.isLt.le i))+(splitIndex G hG x).2.val := by
  have h := finSigmaFinEquiv_apply (splitIndex G hG x)
  have hi : finSigmaFinEquiv (splitIndex G hG x)=finCongr (count_eq_sum_weights G hG) x := by
    simp [splitIndex]
  rw [hi] at h
  exact h

/-- A selected branch always has a real edge and a positive residual count. -/
 theorem selected_edge {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (x : Fin (count ⟨N+1,G⟩)) :
    G.graph.Adj 0 (splitIndex G hG x).1 := by
  have hp := (splitIndex G hG x).2.isLt
  have hw := weight_eq_child G hG (splitIndex G hG x).1
  exact (matchingChildCount_pos G.graph 0 _ (by omega)).1

/-- The bijection counting one named branch includes every residual rank once. -/
def branchFiberEquiv {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (j : Fin (N+1)) :
    {x : Fin (count ⟨N+1,G⟩) // (splitIndex G hG x).1=j} ≃ Fin (weight G j) :=
  (Equiv.subtypeEquivOfSubtype (splitIndex G hG)).trans (Equiv.sigmaSubtype j)

/-- The weighted choice has the exact residual-count probability. This is the
law used at every adaptive deletion state, with actual binary counter outputs. -/
 theorem branch_probability {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (j : Fin (N+1)) :
    probability (fun x : Fin (count ⟨N+1,G⟩) => (splitIndex G hG x).1=j)=
      (weight G j : ℚ)/count ⟨N+1,G⟩ := by
  classical
  rw [probability_eq_card]
  have h := Fintype.card_congr (branchFiberEquiv G hG j)
  simpa only [Fintype.card_eq_nat_card,Nat.card_fin] using congrArg (fun k : ℕ => (k : ℚ)/count ⟨N+1,G⟩) h

 theorem branch_probability_graph {N : ℕ} (G : MatrixGraph (N+1))
    (hG : DistanceHereditaryGraph G.graph) (j : Fin (N+1)) :
    probability (fun x : Fin (count ⟨N+1,G⟩) => (splitIndex G hG x).1=j)=
      (matchingChildCount G.graph 0 j : ℚ)/perfectMatchingCount G.graph := by
  rw [branch_probability G hG j,weight_eq_child G hG j,count_correct _ hG]

end HiddenCircuits.ExactSampling.DHWeights
