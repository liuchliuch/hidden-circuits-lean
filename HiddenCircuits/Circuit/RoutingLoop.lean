import HiddenCircuits.Circuit.EdgeRouting
import HiddenCircuits.Circuit.BoundaryPrograms

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- The emitted gate program, actual updated source-to-wire permutation, and exact swap count. -/
structure RouteResult (n : ℕ) where
  program : ConstraintProgram n
  permutation : Equiv.Perm (Fin n)
  swaps : ℕ

/-- Process each actual source edge while retaining the updated correspondence; no restoration is inserted. -/
def routeEdgeList {n : ℕ} : Equiv.Perm (Fin n) → List (SourceEdge n) → RouteResult n
  | π,[] => ⟨.identity n,π,0⟩
  | π,e::w =>
      let tail := routeEdgeList (edgeRoutePermutation π e) w
      ⟨(edgeProgram π e).compose tail.program,tail.permutation,(edgeRouteIndices π e).length+tail.swaps⟩

def sourceEdgeWeight {n : ℕ} (w : List (SourceEdge n)) (x : CodeBits n) : ℚ :=
  (w.map (fun e => edgePenalty e.left e.right x)).prod

/-- The concrete loop invariant identifies every gate and the complete accumulated graph-edge indicator. -/
theorem routeEdgeList_invariant {n : ℕ} (w : List (SourceEdge n)) (π : Equiv.Perm (Fin n)) :
    wireMatrix π * (routeEdgeList π w).program.matrix =
      Matrix.diagonal (sourceEdgeWeight w) * wireMatrix (routeEdgeList π w).permutation := by
  induction w generalizing π with
  | nil =>
    have hd : Matrix.diagonal (sourceEdgeWeight ([] : List (SourceEdge n))) =
        (1 : Matrix (CodeBits n) (CodeBits n) ℚ) := by
      ext i j
      simp [sourceEdgeWeight,Matrix.diagonal_apply,Matrix.one_apply]
    simp only [routeEdgeList,ConstraintProgram.identity_matrix,hd,mul_one,one_mul]
  | cons e w ih =>
    change wireMatrix π * ((edgeProgram π e).compose (routeEdgeList (edgeRoutePermutation π e) w).program).matrix = _
    rw [ConstraintProgram.compose_matrix,← Matrix.mul_assoc,edgeProgram_invariant,Matrix.mul_assoc,ih,
      ← Matrix.mul_assoc,Matrix.diagonal_mul_diagonal]
    rfl

/-- One edge uses at mostn−1 adjacent exchanges and one N gate, exactly as in the source construction. -/
theorem routeEdgeList_length {n : ℕ} (w : List (SourceEdge n)) (π : Equiv.Perm (Fin n)) :
    (routeEdgeList π w).program.gates.length≤w.length*(9*(n-1)+1) := by
  induction w generalizing π with
  | nil => simp [routeEdgeList,ConstraintProgram.identity]
  | cons e w ih =>
    have h1 := edgeProgram_length π e
    have h2 := ih (edgeRoutePermutation π e)
    change ((edgeProgram π e).gates ++ (routeEdgeList (edgeRoutePermutation π e) w).program.gates).length≤_
    rw [List.length_append]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

 theorem routeEdgeList_swaps {n : ℕ} (w : List (SourceEdge n)) (π : Equiv.Perm (Fin n)) :
    (routeEdgeList π w).swaps≤w.length*(n-1) := by
  induction w generalizing π with
  | nil => simp [routeEdgeList]
  | cons e w ih =>
    have h1 := edgeRoute_length π e
    have h2 := ih (edgeRoutePermutation π e)
    change (edgeRouteIndices π e).length+(routeEdgeList (edgeRoutePermutation π e) w).swaps≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- The entire source routing normalization is the explicit power8^{-number of swaps}. -/
theorem routeEdgeList_scalar {n : ℕ} (w : List (SourceEdge n)) (π : Equiv.Perm (Fin n)) :
    (routeEdgeList π w).program.scalar=(1/8:ℚ)^(routeEdgeList π w).swaps := by
  induction w generalizing π with
  | nil => simp [routeEdgeList,ConstraintProgram.identity]
  | cons e w ih =>
    change (edgeProgram π e).scalar*(routeEdgeList (edgeRoutePermutation π e) w).program.scalar = _
    rw [edgeProgram_scalar,ih,← pow_add]
    rfl

/-- Final reset ignores the accumulated permutation, exactly as required when routes are not restored. -/
theorem wireMatrix_reset_zero {n : ℕ} (π : Equiv.Perm (Fin n)) (x : CodeBits n) :
    (wireMatrix π * resetMatrix n) x (zeroBits n)=1 := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (wirePermutation π x)]
  · simp [wireMatrix,reset_zero_column]
  · intro y _ hy
    simp [wireMatrix,hy]
  · simp

 theorem preparation_permuted_reset (n : ℕ) (π : Equiv.Perm (Fin n)) (weight : CodeBits n → ℚ) :
    (preparationMatrix n * Matrix.diagonal weight * wireMatrix π * resetMatrix n)
      (zeroBits n) (zeroBits n)=∑ x, weight x := by
  rw [Matrix.mul_assoc (preparationMatrix n * Matrix.diagonal weight),Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mul_diagonal,preparation_zero_row,wireMatrix_reset_zero,one_mul,mul_one]

end HiddenCircuits.Circuit
