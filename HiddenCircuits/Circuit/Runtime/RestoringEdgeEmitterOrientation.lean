import HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitterCorrectness

/-! The original matrix-edge orientation changes neither the restoring route
nor its scalar or exact gate bytes. The runtime scan may safely order endpoints. -/
namespace HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter
open HiddenCircuits.Complexity

def lower {n : ℕ} (e : SourceEdge n) : ℕ := min e.left.val e.right.val
def distance {n : ℕ} (e : SourceEdge n) : ℕ := max e.left.val e.right.val-lower e-1

lemma distance_eq {n : ℕ} (e : SourceEdge n) :
    lower e+distance e+1=max e.left.val e.right.val := by
  have hne : e.left.val≠e.right.val := fun h => e.distinct (Fin.ext h)
  dsimp [distance,lower]
  omega

lemma ordered_bound {n : ℕ} (e : SourceEdge n) : lower e+distance e+1<n := by
  rw [distance_eq]
  exact max_lt e.left.isLt e.right.isLt

lemma route_normal_form {n : ℕ} (e : SourceEdge n) :
    edgeRouteIndices (1 : Equiv.Perm (Fin n)) e=
      routeIndices (lower e+1) (distance e) (by have := ordered_bound e;omega) := by
  by_cases h : (1 : Equiv.Perm (Fin n)) e.left<(1 : Equiv.Perm (Fin n)) e.right
  · unfold edgeRouteIndices
    rw [dif_pos h]
    have hv : e.left.val<e.right.val := h
    simp only [Equiv.Perm.one_apply,routeBetween]
    congr 1 <;> dsimp [distance,lower] <;> omega
  · unfold edgeRouteIndices
    rw [dif_neg h]
    have hne : e.left.val≠e.right.val := fun he => e.distinct (Fin.ext he)
    have hv : e.right.val<e.left.val := by change ¬e.left.val<e.right.val at h;omega
    simp only [Equiv.Perm.one_apply,routeBetween]
    congr 1 <;> dsimp [distance,lower] <;> omega

lemma position_normal_form {n : ℕ} (e : SourceEdge n) :
    (edgeRoutePosition (1 : Equiv.Perm (Fin n)) e).val=lower e := by
  by_cases h : (1 : Equiv.Perm (Fin n)) e.left<(1 : Equiv.Perm (Fin n)) e.right
  · unfold edgeRoutePosition
    rw [dif_pos h]
    have hv : e.left.val<e.right.val := h
    exact (min_eq_left hv.le).symm
  · unfold edgeRoutePosition
    rw [dif_neg h]
    have hv : e.right.val≤e.left.val := by change ¬e.left.val<e.right.val at h;omega
    exact (min_eq_right hv).symm

/-- Exact program equality, including its scalar field and complete gate list,
for either matrix orientation of the same unordered edge. -/
theorem restoringEdgeProgram_ordered {n : ℕ} (e : SourceEdge n) :
    restoringEdgeProgram e=restoringEdgeProgram (orderedEdge (lower e) (distance e) (ordered_bound e)) := by
  have hroute : edgeRouteIndices (1 : Equiv.Perm (Fin n)) e=
      edgeRouteIndices (1 : Equiv.Perm (Fin n)) (orderedEdge (lower e) (distance e) (ordered_bound e)) := by
    rw [ordered_route,route_normal_form]
  have hpos : edgeRoutePosition (1 : Equiv.Perm (Fin n)) e=
      edgeRoutePosition (1 : Equiv.Perm (Fin n)) (orderedEdge (lower e) (distance e) (ordered_bound e)) := by
    apply Fin.ext
    rw [position_normal_form,ordered_position]
  simp only [restoringEdgeProgram,edgeProgram,hroute,hpos]

/-- The local emitter's actual output is exactly the original source edge's
canonical bytes after the outer scan computes min and the endpoint gap. -/
theorem bits_eq_unordered_edge {n : ℕ} (e : SourceEdge n) :
    bits (lower e) (distance e)=encodeBitList ((restoringEdgeProgram e).gates.map gateBits) := by
  rw [restoringEdgeProgram_ordered]
  exact bits_eq_restoringEdge _ _ _

theorem unordered_normalization {n : ℕ} (e : SourceEdge n) :
    (restoringEdgeProgram e).scalar=(1/8:ℚ)^(2*(distance e)) ∧
      (restoringEdgeProgram e).gates.length=18*(distance e)+1 := by
  rw [restoringEdgeProgram_ordered]
  exact ordered_normalization _ _ _

theorem unordered_edge_executes {n : ℕ} (g : BitString → ℕ) (e : SourceEdge n) (out : BitString) :
    ∃ cost, program.Executes g (store (lower e) (distance e) 0 0 out [] [] [])
      (store (lower e) (distance e) 0 0 ((encodeBitList ((restoringEdgeProgram e).gates.map gateBits)).reverse++out) [] [] []) cost ∧
      cost≤timeBound.eval (lower e+distance e) := by
  rw [←bits_eq_unordered_edge e]
  exact program_executes g _ _ out

end HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter
