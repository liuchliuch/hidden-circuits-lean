import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualProgram
import HiddenCircuits.GraphIsomorphismCount
import HiddenCircuits.Approximation.Relabeling
import HiddenCircuits.Complexity.GraphVerifier.MatchingCertificates

/-! Exact dense pair-deletion mathematics. The count interpretation requires a
legal selected edge; arbitrary or rejected branches are never interpreted as
an unconstrained smaller graph. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidual
open Complexity Initialization

lemma retained_card {N : ℕ} (j : Fin (N+1)) (hj : j≠0) : (retained j).card+2=N+1 := by
  unfold retained
  rw [Finset.card_erase_of_mem (by simp [hj]),Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ,Fintype.card_fin]
  have hN : 0<N := by
    have h := j.isLt
    have hj' : j.val≠0 := by simpa using hj
    omega
  omega

def retainedEquiv {N : ℕ} (j : Fin (N+1)) : (retained j) ≃ withoutPair (0:Fin (N+1)) j :=
  Equiv.subtypeEquivRight (fun i => by simp [retained,withoutPair,and_comm])

noncomputable def graphIso {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    (graph G j).graph ≃g G.graph.induce (withoutPair (0:Fin (N+1)) j) where
  toEquiv := (Finset.orderIsoOfFin (retained j) rfl).toEquiv.trans (retainedEquiv j)
  map_rel_iff' := by intro i k;rfl

lemma graph_count {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    perfectMatchingCount (graph G j).graph=perfectMatchingCount (G.graph.induce (withoutPair (0:Fin (N+1)) j)) :=
  perfectMatchingCount_congr (graphIso G j)

/-- Only a legal edge admits the residual/fiber interpretation. -/
theorem graph_count_fiber {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1))
    (hj : G.graph.Adj 0 j) :
    perfectMatchingCount (graph G j).graph=Fintype.card (EdgeFiber G.graph 0 j) := by
  rw [graph_count,perfectMatchingCount_eq_partners]
  exact (Fintype.card_congr (edgeDeletionEquiv hj)).symm

theorem output_fiber_count {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1))
    (hj : G.graph.Adj 0 j) :
    GraphInput.perfectMatchingProblem (output G j)=Fintype.card (EdgeFiber G.graph 0 j) := by
  simp only [output,GraphInput.perfectMatchingProblem,GraphInput.decode_encode]
  exact graph_count_fiber G j hj

lemma retained_card_even {d : ℕ} (j : Fin (2*(d+1))) (hj : j≠0) : (retained j).card=2*d := by
  have h := retained_card j hj
  change (retained j).card+2=2*d+2 at h
  omega

/-- The inherited increasing embedding of the exact remaining vertices. -/
def evenEmbedding {d : ℕ} (j : Fin (2*(d+1))) (hj : j≠0) : Fin (2*d) ↪ Fin (2*(d+1)) :=
  ((retained j).orderEmbOfFin (retained_card_even j hj)).toEmbedding

/-- Typed even residual used by rank-decreasing counting states. It is the
same inherited-order dense graph physically emitted by the program. -/
def evenGraph {d : ℕ} (G : MatrixGraph (2*(d+1))) (j : Fin (2*(d+1))) (hj : j≠0) : MatrixGraph (2*d) :=
  InducedGraphEmitter.graph G (evenEmbedding j hj)

lemma evenGraph_eq_comap {d : ℕ} (G : MatrixGraph (2*(d+1))) (j : Fin (2*(d+1))) (hj : j≠0) :
    (evenGraph G j hj).graph=G.graph.comap (evenEmbedding j hj) := rfl

lemma evenGraph_quasimonotone {d : ℕ} (G : MatrixGraph (2*(d+1))) (j : Fin (2*(d+1)))
    (hj : j≠0) (hG : Quasimonotone G.graph) : Quasimonotone (evenGraph G j hj).graph :=
  hG.comap (evenEmbedding j hj) (evenEmbedding j hj).injective

lemma induced_input_cast {N m : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (h : U.card=m) :
    (⟨U.card,InducedGraphEmitter.graph G (U.orderEmbOfFin rfl)⟩ : GraphInput)=
      ⟨m,InducedGraphEmitter.graph G (U.orderEmbOfFin h)⟩ := by
  cases h
  rfl

lemma output_as_evenGraph {d : ℕ} (G : MatrixGraph (2*(d+1))) (j : Fin (2*(d+1))) (hj : j≠0) :
    output G j=GraphInput.encode ⟨2*d,evenGraph G j hj⟩ := by
  apply congrArg GraphInput.encode
  exact induced_input_cast G (retained j) (retained_card_even j hj)

lemma evenGraph_count_fiber {d : ℕ} (G : MatrixGraph (2*(d+1))) (j : Fin (2*(d+1)))
    (hj : G.graph.Adj 0 j) :
    perfectMatchingCount (evenGraph G j hj.ne.symm).graph=Fintype.card (EdgeFiber G.graph 0 j) := by
  have h := output_fiber_count G j hj
  rw [output_as_evenGraph G j hj.ne.symm] at h
  simpa only [GraphInput.perfectMatchingProblem,GraphInput.decode_encode] using h

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidual
