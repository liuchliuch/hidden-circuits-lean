import HiddenCircuits.GraphReduction.MonotoneEndpointDecode
import HiddenCircuits.Complexity.GraphVerifier.MatchingFinalRuntime
import HiddenCircuits.Complexity.MatrixEmitterGraph
import HiddenCircuits.GraphReduction.Runtime.ListLookup
import HiddenCircuits.GraphReduction.Runtime.UnaryCompare
import HiddenCircuits.GraphReduction.Runtime.LocalCleanup

/-! Literal endpoint-to-bipartite-graph translation. This module does not
assume a graph representation in the input; graph bytes are a computed output. -/
namespace HiddenCircuits.GraphReduction.Runtime.EndpointGraph
open Complexity OracleBlock Approximation MonotoneEndpointEncoding
set_option maxHeartbeats 900000

def endpoint {n : ℕ} (f : Fin n → ℕ) (i : ℕ) : ℕ := if h:i<n then f ⟨i,h⟩ else 0
def edge (n : ℕ) (lo hi : ℕ → ℕ) (i j : ℕ) : Bool :=
  (decide (i<n) && !decide (j<n) && !decide (j-n<lo i) && decide (j-n<hi i)) ||
  (decide (j<n) && !decide (i<n) && !decide (i-n<lo j) && decide (i-n<hi j))
lemma edge_symm (n : ℕ) (lo hi : ℕ → ℕ) (i j : ℕ) : edge n lo hi i j=edge n lo hi j i := by
  unfold edge;rw [Bool.or_comm]
lemma edge_loopless (n : ℕ) (lo hi : ℕ → ℕ) (i : ℕ) : edge n lo hi i i=false := by
  by_cases h:i<n <;> simp [edge,h]

def matrix {n : ℕ} (E : MonotoneEndpoints n) : MatrixGraph (n+n) where
  edge i j := edge n (endpoint E.lo) (endpoint E.hi) i.val j.val
  symm i j := edge_symm _ _ _ _ _
  loopless i := edge_loopless _ _ _ _
def graph (E : Input) : GraphInput := ⟨E.1+E.1,matrix E.2⟩
def relation {n : ℕ} (E : MonotoneEndpoints n) (i j : Fin n) : Prop := E.lo i ≤ j.val ∧ j.val < E.hi i
instance {n : ℕ} (E : MonotoneEndpoints n) : DecidableRel (relation E) := fun i j => by unfold relation;infer_instance

noncomputable def graphIso {n : ℕ} (E : MonotoneEndpoints n) : cutGraph (relation E) ≃g (matrix E).graph where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by
    intro i j
    rcases i with i|i <;> rcases j with j|j <;>
      simp [matrix,MatrixGraph.graph,edge,endpoint,relation,cutGraph,SimpleGraph.fromRel_adj,
        finSumFinEquiv,i.isLt,j.isLt,show ¬n+i.val<n by omega,show ¬n+j.val<n by omega,Nat.add_sub_cancel_left]

theorem graph_count (E : Input) : perfectMatchingCount (graph E).2.graph=Fintype.card E.2.Permutations := by
  rcases E with ⟨n,E⟩
  change perfectMatchingCount (matrix E).graph=_
  rw [←perfectMatchingCount_congr (graphIso E)]
  exact Fintype.card_congr (cutPerfectMatchingEquiv (relation E))

def rejectedGraph : GraphInput := ⟨1,⟨fun _ _ => false,by intros;rfl,by intros;rfl⟩⟩
lemma rejectedGraph_bits : rejectedGraph.encode=[true,true,false,false] := by decide
lemma rejectedGraph_count : perfectMatchingCount rejectedGraph.2.graph=0 := by
  letI : IsEmpty (PerfectMatching rejectedGraph.2.graph) := ⟨fun M => by
    obtain ⟨v,hv,_⟩ := M.property.1 (M.property.2 (0:Fin 1))
    exact Bool.false_ne_true (M.val.adj_sub hv)⟩
  exact Fintype.card_eq_zero

def compiledBits (xs : BitString) : BitString := match decode xs with
  | none => rejectedGraph.encode
  | some E => (graph E).encode

theorem count_eq_compiled (xs : BitString) : count xs=GraphInput.perfectMatchingProblem (compiledBits xs) := by
  unfold count compiledBits
  cases h:decode xs with
  | none => simp [GraphInput.perfectMatchingProblem,rejectedGraph_count]
  | some E => simp [GraphInput.perfectMatchingProblem,graph_count]

lemma compiled_size (xs : BitString) : (compiledBits xs).length ≤ 8*(xs.length+1)^2 := by
  unfold compiledBits
  cases h:decode xs with
  | none =>
    rw [rejectedGraph_bits]
    simp only [List.length_cons,List.length_nil]
    have hh : 1 ≤ (xs.length+1)^2 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) _)
    omega
  | some E =>
    have hn := MonotoneEndpointEncoding.size_le_of_decode h
    rw [GraphInput.encode_length]
    change 2*(E.1+E.1)+(E.1+E.1)*(E.1+E.1)+1 ≤ _
    nlinarith

lemma row_lookup {n : ℕ} (f : Fin n → ℕ) (j : ℕ) : ((rows f)[j]?.getD [])=List.replicate (endpoint f j) true := by
  by_cases hj:j<n
  · simp [rows,endpoint,hj,List.getElem?_ofFn]
  · have hh : (rows f)[j]?=none := List.getElem?_eq_none (by simpa [rows] using Nat.le_of_not_gt hj)
    simp [hh,endpoint,hj]
end HiddenCircuits.GraphReduction.Runtime.EndpointGraph
