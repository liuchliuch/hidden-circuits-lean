import HiddenCircuits.Complexity.CNFCloning
import HiddenCircuits.Complexity.GraphRelabel

/-! Explicit finite clone-vertex enumeration, canonical binary graph queries,
and correctness and size bridges. -/
namespace HiddenCircuits.Complexity.CNF
open scoped BigOperators
variable {n m : ℕ} (F : CNF n m)

/-- Split cloned variable vertices from cloned clause vertices. -/
def cloneVertexSplit (a b : ℕ) :
    Cloning.Vertex (cloneMultiplicity (n := n) (m := m) a b) ≃
      ((Fin n × Bool) × Fin a) ⊕ (Fin m × Fin b) where
  toFun u := match u with
    | ⟨.inl v,i⟩ => .inl (v,i)
    | ⟨.inr v,i⟩ => .inr (v,i)
  invFun u := match u with
    | .inl (v,i) => ⟨.inl v,i⟩
    | .inr (v,i) => ⟨.inr v,i⟩
  left_inv u := by rcases u with ⟨u,i⟩; cases u <;> rfl
  right_inv u := by cases u <;> rfl

/-- This is an explicit arithmetic enumeration, with no choice of a `Fintype`
enumeration hidden in the graph construction. -/
def cloneVertexFinEquiv (a b : ℕ) :
    Cloning.Vertex (cloneMultiplicity (n := n) (m := m) a b) ≃ Fin (n*2*a+m*b) :=
  (cloneVertexSplit a b).trans
    ((Equiv.sumCongr
      (((Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finProdFinEquiv).prodCongr
        (Equiv.refl (Fin a)) |>.trans finProdFinEquiv)
      finProdFinEquiv).trans finSumFinEquiv)

instance cloneGraphDecidable (a b : ℕ) : DecidableRel (F.cloneGraph a b).Adj := by
  intro u v
  change Decidable ((u.1 = v.1 ∧ u ≠ v) ∨ F.graph.Adj u.1 v.1)
  infer_instance

/-- Actual Boolean matrix emitted for an ordinary independent-set oracle query. -/
def cloneQuery (a b : ℕ) : GraphInput :=
  ⟨n*2*a+m*b,MatrixGraph.relabel (F.cloneGraph a b) (cloneVertexFinEquiv a b)⟩

/-- Encoding changes no independent-set count. -/
theorem cloneQuery_count (a b : ℕ) :
    (F.cloneQuery a b).2.independentCount = F.cloneCount a b := by
  unfold cloneQuery MatrixGraph.independentCount cloneCount
  exact Fintype.card_congr
    (MatrixGraph.relabelIndependentEquiv (F.cloneGraph a b) (cloneVertexFinEquiv a b)).symm

/-- The oracle receives these actual binary strings, including graph order and
all adjacency bits. -/
def encodedCloneQuery (a b : ℕ) : BitString := GraphInput.encode (F.cloneQuery a b)

@[simp] theorem encodedCloneQuery_correct (a b : ℕ) :
    GraphInput.independentSetProblem (F.encodedCloneQuery a b) = F.cloneCount a b := by
  rw [encodedCloneQuery,GraphInput.independentSetProblem_encode,F.cloneQuery_count]

/-- End-to-end algebraic #SAT recovery calls the total binary-input graph oracle. -/
theorem satCount_from_encoded_independent_queries :
    recoverGrid n m n (fun i j =>
      (GraphInput.independentSetProblem (F.encodedCloneQuery i.val j.val) : ℚ)) =
    (F.satCount : ℚ) := by
  simp only [encodedCloneQuery_correct]
  exact F.satCount_from_independent_counts

@[simp] theorem encodedCloneQuery_length (a b : ℕ) :
    (F.encodedCloneQuery a b).length = 2*(n*2*a+m*b)+(n*2*a+m*b)^2+1 := by
  rw [encodedCloneQuery,GraphInput.encode_length]
  simp only [cloneQuery]
  ring

/-- The literal binary query length is polynomial, including every adjacency bit. -/
theorem encodedCloneQuery_grid_length (i : Fin (n+1)) (j : Fin (m+1)) :
    (F.encodedCloneQuery i.val j.val).length ≤ (2*n+m+1)^4 := by
  rw [encodedCloneQuery_length]
  have hi : i.val ≤ n := interpolation_node_bound i
  have hj : j.val ≤ m := interpolation_node_bound j
  have hv : n*2*i.val+m*j.val ≤ (2*n+m)^2 := by
    have hni := Nat.mul_le_mul_left (n*2) hi
    have hmj := Nat.mul_le_mul_left m hj
    nlinarith
  have hs : (n*2*i.val+m*j.val)^2 ≤ ((2*n+m)^2)^2 := Nat.pow_le_pow_left hv 2
  nlinarith

/-- Actual binary oracle answers also have polynomial length on the query grid. -/
theorem encodedCloneAnswer_grid_length (i : Fin (n+1)) (j : Fin (m+1)) :
    (Computability.encodeNat (GraphInput.independentSetProblem
      (F.encodedCloneQuery i.val j.val))).length ≤ (2*n+m)^2+1 := by
  rw [encodeNat_length,encodedCloneQuery,GraphInput.independentSetProblem_encode]
  have h := Nat.size_le_size ((F.cloneQuery i.val j.val).2.independentCount_le)
  rw [Nat.size_pow] at h
  have hi := interpolation_node_bound i
  have hj := interpolation_node_bound j
  have hni := Nat.mul_le_mul_left (n*2) hi
  have hmj := Nat.mul_le_mul_left m hj
  change ((F.cloneQuery i.val j.val).2.independentCount).size ≤ (2*n+m)^2+1
  change ((F.cloneQuery i.val j.val).2.independentCount).size ≤ n*2*i.val+m*j.val+1 at h
  nlinarith

end HiddenCircuits.Complexity.CNF
