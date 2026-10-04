import HiddenCircuits.Circuit.SourceCircuit

/-! A concrete source circuit that restores wire order after every edge. It has
its own explicit normalization and polynomial bound; the original paper's
one-way route and sharper gate count remain the separate SourceCircuit theorem. -/
namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- Route one actual edge, apply its forbid gate, then undo the literal route. -/
def restoringEdgeProgram {n : ℕ} (e : SourceEdge n) : ConstraintProgram n :=
  (edgeProgram 1 e).compose (routeProgram (edgeRouteIndices 1 e).reverse)

theorem restoringEdgeProgram_matrix {n : ℕ} (e : SourceEdge n) :
    (restoringEdgeProgram e).matrix=Matrix.diagonal (edgePenalty e.left e.right) := by
  have he := edgeProgram_invariant (1 : Equiv.Perm (Fin n)) e
  rw [wireMatrix_one,one_mul] at he
  rw [restoringEdgeProgram,ConstraintProgram.compose_matrix,he,routeProgram_matrix,
    executeSwaps_reverse]
  simp only [edgeRoutePermutation,mul_one,Matrix.mul_assoc]
  rw [show (executeSwaps (edgeRouteIndices 1 e)).symm=(executeSwaps (edgeRouteIndices 1 e))⁻¹ from rfl,
    wireMatrix_inverse,mul_one]

theorem restoringEdgeProgram_length {n : ℕ} (e : SourceEdge n) :
    (restoringEdgeProgram e).gates.length=18*(edgeRouteIndices 1 e).length+1 := by
  simp only [restoringEdgeProgram,edgeProgram,ConstraintProgram.compose,List.length_append,
    routeProgram_length,List.length_reverse,List.length_cons,List.length_nil]
  omega

theorem restoringEdgeProgram_scalar {n : ℕ} (e : SourceEdge n) :
    (restoringEdgeProgram e).scalar=(1/8 : ℚ)^(2*(edgeRouteIndices 1 e).length) := by
  simp only [restoringEdgeProgram,ConstraintProgram.compose,edgeProgram_scalar,routeProgram_scalar,
    List.length_reverse,←pow_add]
  congr 1
  omega

def restoringEdges {n : ℕ} : List (SourceEdge n) → ConstraintProgram n
  | [] => .identity n
  | e::es => (restoringEdgeProgram e).compose (restoringEdges es)

def restoringSwapPairs {n : ℕ} (es : List (SourceEdge n)) : ℕ :=
  (es.map (fun e => (edgeRouteIndices 1 e).length)).sum

theorem restoringEdges_matrix {n : ℕ} (es : List (SourceEdge n)) :
    (restoringEdges es).matrix=Matrix.diagonal (sourceEdgeWeight es) := by
  induction es with
  | nil =>
    ext x y
    simp [restoringEdges,ConstraintProgram.identity_matrix,sourceEdgeWeight,Matrix.diagonal_apply,Matrix.one_apply]
  | cons e es ih =>
    rw [restoringEdges,ConstraintProgram.compose_matrix,restoringEdgeProgram_matrix,ih,Matrix.diagonal_mul_diagonal]
    rfl

theorem restoringEdges_scalar {n : ℕ} (es : List (SourceEdge n)) :
    (restoringEdges es).scalar=(1/8 : ℚ)^(2*restoringSwapPairs es) := by
  induction es with
  | nil => simp [restoringEdges,ConstraintProgram.identity,restoringSwapPairs]
  | cons e es ih =>
    simp only [restoringEdges,ConstraintProgram.compose,restoringEdgeProgram_scalar,ih,←pow_add,
      restoringSwapPairs,List.map_cons,List.sum_cons]
    congr 1
    ring

theorem restoringEdges_length {n : ℕ} (es : List (SourceEdge n)) :
    (restoringEdges es).gates.length=18*restoringSwapPairs es+es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [restoringEdges,ConstraintProgram.compose,List.length_append,restoringEdgeProgram_length,
      ih,restoringSwapPairs,List.map_cons,List.sum_cons,List.length_cons]
    ring

theorem restoringSwapPairs_bound {n : ℕ} (es : List (SourceEdge n)) :
    restoringSwapPairs es≤es.length*(n-1) := by
  induction es with
  | nil => simp [restoringSwapPairs]
  | cons e es ih =>
    have h := edgeRoute_length (1 : Equiv.Perm (Fin n)) e
    simp only [restoringSwapPairs,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

def restoringIndependentProgram {n : ℕ} (G : Complexity.MatrixGraph n) : ConstraintProgram n :=
  ((preparationProgram n).compose (restoringEdges (sourceEdges G))).compose (resetProgram n)

theorem restoringIndependentProgram_correct {n : ℕ} (G : Complexity.MatrixGraph n) :
    (restoringIndependentProgram G).matrix (zeroBits n) (zeroBits n)=G.independentCount := by
  rw [restoringIndependentProgram,ConstraintProgram.compose_matrix,ConstraintProgram.compose_matrix,
    preparationProgram_matrix,resetProgram_matrix,restoringEdges_matrix]
  have h := preparation_permuted_reset n (1 : Equiv.Perm (Fin n)) (sourceEdgeWeight (sourceEdges G))
  simp only [wireMatrix_one,mul_one] at h
  rw [h]
  simp_rw [sourceEdges_indicator]
  exact independent_indicator_sum G

theorem restoringIndependentProgram_scalar {n : ℕ} (G : Complexity.MatrixGraph n) :
    (restoringIndependentProgram G).scalar=(1/8 : ℚ)^(2*restoringSwapPairs (sourceEdges G)) := by
  simp only [restoringIndependentProgram,ConstraintProgram.compose,preparationProgram,resetProgram,
    uniformOneProgram_scalar,one_mul,mul_one,restoringEdges_scalar]

theorem restoringIndependentProgram_length {n : ℕ} (G : Complexity.MatrixGraph n) :
    (restoringIndependentProgram G).gates.length≤2*n+n^2*(18*n+1) := by
  have he := orderedEdges_length_bound G
  have hs := restoringSwapPairs_bound (sourceEdges G)
  rw [sourceEdges_length] at hs
  simp only [restoringIndependentProgram,ConstraintProgram.compose,List.length_append,
    preparationProgram,resetProgram,uniformOneProgram_length,restoringEdges_length,sourceEdges_length]
  have hsn : restoringSwapPairs (sourceEdges G)≤n^2*n := by
    calc
      _ ≤ (orderedEdges G).length*(n-1) := hs
      _ ≤ (n*n)*n := Nat.mul_le_mul he (by omega)
      _ = _ := by ring
  nlinarith

end HiddenCircuits.Circuit
