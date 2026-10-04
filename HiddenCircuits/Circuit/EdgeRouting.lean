import HiddenCircuits.Circuit.RoutedWire
import HiddenCircuits.Circuit.PlacedConstraints

namespace HiddenCircuits.Circuit

/-- An actual pair of distinct source vertices, rather than an assumed wire-local constraint. -/
structure SourceEdge (n : ℕ) where
  left : Fin n
  right : Fin n
  distinct : left≠right

 theorem permuted_edge_ne {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) :
    (π e.left).val≠(π e.right).val := fun h => e.distinct (π.injective (Fin.ext h))

def edgeRouteIndices {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) : List (Fin (n-1)) :=
  if h:π e.left<π e.right then routeBetween (π e.left) (π e.right) h
  else routeBetween (π e.right) (π e.left) (by
    have hn := permuted_edge_ne π e
    change ¬ (π e.left).val < (π e.right).val at h
    change (π e.right).val < (π e.left).val
    omega)

def edgeRoutePosition {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) : Fin (n-1) :=
  if h:π e.left<π e.right then ⟨(π e.left).val,by have hb:=(π e.right).isLt;change (π e.left).val<(π e.right).val at h;omega⟩
  else ⟨(π e.right).val,by have ha:=(π e.left).isLt;have hn:=permuted_edge_ne π e;change ¬(π e.left).val<(π e.right).val at h;omega⟩

def edgeRoutePermutation {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) : Equiv.Perm (Fin n) :=
  executeSwaps (edgeRouteIndices π e) * π

/-- The exact source endpoints occupy the two neighboring target positions, possibly in reversed order. -/
theorem edgeRoute_spec {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) :
    let p := adjacentPlacement (edgeRoutePosition π e)
    (edgeRoutePermutation π e e.left=p.activeTrack 0 ∧ edgeRoutePermutation π e e.right=p.activeTrack 1) ∨
    (edgeRoutePermutation π e e.right=p.activeTrack 0 ∧ edgeRoutePermutation π e e.left=p.activeTrack 1) := by
  dsimp only
  by_cases h:π e.left<π e.right
  · have hs := routeBetween_spec (π e.left) (π e.right) h
    left
    simp only [edgeRoutePermutation,edgeRouteIndices,edgeRoutePosition,dif_pos h,Equiv.Perm.mul_apply,
      adjacentPlacement,Placement.activeTrack,Fin.val_zero,Fin.val_one,Nat.add_zero]
    exact ⟨hs.2.2.1,hs.2.2.2⟩
  · have hb : π e.right<π e.left := by
      have hn := permuted_edge_ne π e
      change ¬(π e.left).val<(π e.right).val at h
      change (π e.right).val<(π e.left).val
      omega
    have hs := routeBetween_spec (π e.right) (π e.left) hb
    right
    simp only [edgeRoutePermutation,edgeRouteIndices,edgeRoutePosition,dif_neg h,Equiv.Perm.mul_apply,
      adjacentPlacement,Placement.activeTrack,Fin.val_zero,Fin.val_one,Nat.add_zero]
    exact ⟨hs.2.2.1,hs.2.2.2⟩

 theorem edgeRoute_length {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) :
    (edgeRouteIndices π e).length≤n-1 := by
  unfold edgeRouteIndices
  split_ifs with h
  · exact (routeBetween_spec _ _ h).2.1
  · exact (routeBetween_spec _ _ _).2.1

/-- Relabeling by the emitted route restores precisely the original source-edge condition. -/
theorem edgeRoute_penalty {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) (x : CodeBits n) :
    edgePenalty ((adjacentPlacement (edgeRoutePosition π e)).activeTrack 0)
      ((adjacentPlacement (edgeRoutePosition π e)).activeTrack 1)
      (wirePermutation (edgeRoutePermutation π e) x) = edgePenalty e.left e.right x := by
  unfold edgePenalty
  rw [wirePermutation_bits,wirePermutation_bits]
  rcases edgeRoute_spec π e with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · rw [← h0,← h1,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  · rw [← h0,← h1,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    simp only [and_comm]

/-- The paper's actual route followed by one adjacent N gate. -/
def edgeProgram {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) : ConstraintProgram n :=
  (routeProgram (edgeRouteIndices π e)).compose
    ⟨1,[.forbid (adjacentPlacement (edgeRoutePosition π e))]⟩

/-- Updating the source-to-wire correspondence is proved at the level of actual gate matrices. -/
theorem edgeProgram_invariant {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) :
    wireMatrix π * (edgeProgram π e).matrix =
      Matrix.diagonal (edgePenalty e.left e.right) * wireMatrix (edgeRoutePermutation π e) := by
  rw [edgeProgram,ConstraintProgram.compose_matrix,routeProgram_matrix]
  have hg : (ConstraintProgram.matrix (n:=n)
      ⟨1,[.forbid (adjacentPlacement (edgeRoutePosition π e))]⟩) =
      Matrix.diagonal (edgePenalty ((adjacentPlacement (edgeRoutePosition π e)).activeTrack 0)
        ((adjacentPlacement (edgeRoutePosition π e)).activeTrack 1)) := by
    simp only [ConstraintProgram.matrix,constraintCircuitMatrix,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,one_smul,adjacent_forbid_diagonal]
  rw [hg,← Matrix.mul_assoc,wireMatrix_mul,wireMatrix_diagonal]
  congr 1
  congr 1
  funext x
  exact edgeRoute_penalty π e x

 theorem edgeProgram_length {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) :
    (edgeProgram π e).gates.length≤9*(n-1)+1 := by
  simp only [edgeProgram,ConstraintProgram.compose,List.length_append,List.length_cons,List.length_nil,
    routeProgram_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 9 (edgeRoute_length π e)) 1

 theorem edgeProgram_scalar {n : ℕ} (π : Equiv.Perm (Fin n)) (e : SourceEdge n) :
    (edgeProgram π e).scalar=(1/8:ℚ)^(edgeRouteIndices π e).length := by
  simp only [edgeProgram,ConstraintProgram.compose,routeProgram_scalar,mul_one]

end HiddenCircuits.Circuit
