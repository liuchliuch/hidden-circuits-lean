import HiddenCircuits.Circuit.RoutingLoop

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- The actual finite graph-edge list supplies distinct endpoints to the routing algorithm. -/
def sourceEdges {n : ℕ} (G : Complexity.MatrixGraph n) : List (SourceEdge n) :=
  (orderedEdges G).attach.map (fun e => ⟨e.val.1,e.val.2,orderedEdges_ne G _ _ e.property⟩)

 theorem sourceEdges_forget {n : ℕ} (G : Complexity.MatrixGraph n) :
    (sourceEdges G).map (fun e => (e.left,e.right))=orderedEdges G := by
  simp [sourceEdges,List.map_map,Function.comp_def,List.attach_map_subtype_val]

 theorem sourceEdges_length {n : ℕ} (G : Complexity.MatrixGraph n) :
    (sourceEdges G).length=(orderedEdges G).length := by simp [sourceEdges]

 theorem sourceEdges_indicator {n : ℕ} (G : Complexity.MatrixGraph n) (x : CodeBits n) :
    sourceEdgeWeight (sourceEdges G) x=if codeIndependent G x then 1 else 0 := by
  have h := congrArg (fun w : List (Fin n × Fin n) => (w.map (fun e => edgePenalty e.1 e.2 x)).prod)
    (sourceEdges_forget G)
  simp only [List.map_map,Function.comp_def] at h
  exact h.trans (orderedEdges_indicator G x)

/-- The complete explicit source circuit: prepare, route each actual graph edge, then reset. -/
def independentSetProgram {n : ℕ} (G : Complexity.MatrixGraph n) : ConstraintProgram n :=
  ((preparationProgram n).compose (routeEdgeList 1 (sourceEdges G)).program).compose (resetProgram n)

/-- Proposition8.1's mathematical circuit identity for actual source graphs and actual primitive gates. -/
theorem independentSetProgram_correct {n : ℕ} (G : Complexity.MatrixGraph n) :
    (independentSetProgram G).matrix (zeroBits n) (zeroBits n)=G.independentCount := by
  have hr := routeEdgeList_invariant (sourceEdges G) (1 : Equiv.Perm (Fin n))
  rw [wireMatrix_one,one_mul] at hr
  rw [independentSetProgram,ConstraintProgram.compose_matrix,ConstraintProgram.compose_matrix,
    preparationProgram_matrix,resetProgram_matrix,hr]
  rw [← Matrix.mul_assoc (preparationMatrix n),preparation_permuted_reset]
  simp_rw [sourceEdges_indicator]
  exact independent_indicator_sum G

/-- Exact scalar normalization as a power of1/8, with the actual number of adjacent exchanges. -/
theorem independentSetProgram_scalar {n : ℕ} (G : Complexity.MatrixGraph n) :
    (independentSetProgram G).scalar=(1/8:ℚ)^(routeEdgeList 1 (sourceEdges G)).swaps := by
  simp only [independentSetProgram,ConstraintProgram.compose,preparationProgram,resetProgram,
    uniformOneProgram_scalar,routeEdgeList_scalar,one_mul,mul_one]

/-- All preparation/reset gates and all nine-gate exchanges are included in the emitted circuit size. -/
theorem independentSetProgram_length {n : ℕ} (G : Complexity.MatrixGraph n) :
    (independentSetProgram G).gates.length≤2*n+(orderedEdges G).length*(9*(n-1)+1) := by
  have h := routeEdgeList_length (sourceEdges G) (1 : Equiv.Perm (Fin n))
  rw [sourceEdges_length] at h
  simp only [independentSetProgram,ConstraintProgram.compose,List.length_append,preparationProgram,
    resetProgram,uniformOneProgram_length]
  omega

/-- The graph input size also bounds the emitted adjacency list directly. -/
theorem orderedEdges_length_bound {n : ℕ} (G : Complexity.MatrixGraph n) :
    (orderedEdges G).length≤n*n := by
  have bound : ∀ (w : List (Fin n)),
      (w.flatMap (fun u => ((List.finRange n).filter (fun v => G.edge u v)).map (fun v => (u,v)))).length≤w.length*n := by
    intro w
    induction w with
    | nil => simp
    | cons u w ih =>
      have hh := List.length_filter_le (fun v => G.edge u v) (List.finRange n)
      simp only [List.length_finRange] at hh
      simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons]
      nlinarith
  simpa only [orderedEdges,List.length_finRange] using bound (List.finRange n)

 theorem independentSetProgram_polynomial_length {n : ℕ} (G : Complexity.MatrixGraph n) :
    (independentSetProgram G).gates.length≤2*n+n^2*(9*n+1) := by
  have h1 := orderedEdges_length_bound G
  have h2 : 9*(n-1)+1≤9*n+1 := by omega
  exact (independentSetProgram_length G).trans
    (Nat.add_le_add_left (by simpa [pow_two] using Nat.mul_le_mul h1 h2) _)

/-- Edgeless source graphs are handled directly, including the zero-vertex input. -/
theorem independentCount_edgeless {n : ℕ} (G : Complexity.MatrixGraph n) (h : orderedEdges G=[]) :
    G.independentCount=2^n := by
  have hs := independent_indicator_sum G
  simp_rw [← orderedEdges_indicator G] at hs
  rw [h] at hs
  have he : (G.independentCount : ℚ)=(2^n : ℕ) := by
    simpa only [List.map_nil,List.prod_nil,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      codeBits_card] using hs.symm
  exact_mod_cast he

/-- The source oracle output is a fixed boundary entry times a completely specified rational scalar. -/
theorem independentSet_circuit_entry {n : ℕ} (G : Complexity.MatrixGraph n) :
    (independentSetProgram G).scalar *
      constraintCircuitMatrix (independentSetProgram G).gates (zeroBits n) (zeroBits n)=G.independentCount :=
  independentSetProgram_correct G

end HiddenCircuits.Circuit
