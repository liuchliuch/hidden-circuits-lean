import HiddenCircuits.Circuit.BitAssignments

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- Literal two-vertex N constraint on an assignment. -/
def edgePenalty {n : ℕ} (u v : Fin n) (x : CodeBits n) : ℚ :=
  if bitsToAssignment n x u=true ∧ bitsToAssignment n x v=true then 0 else 1

/-- Nonedges contribute the multiplicative identity. -/
def graphEdgePenalty {n : ℕ} (G : Complexity.MatrixGraph n) (u v : Fin n) (x : CodeBits n) : ℚ :=
  if G.edge u v then edgePenalty u v x else 1

/-- The product of the genuine forbidden11 factors is exactly the independent-set indicator. -/
theorem edge_penalty_indicator {n : ℕ} (G : Complexity.MatrixGraph n) (x : CodeBits n) :
    (∏ u : Fin n, ∏ v : Fin n, graphEdgePenalty G u v x) =
      if codeIndependent G x then 1 else 0 := by
  classical
  by_cases h:codeIndependent G x
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro u _
    apply Finset.prod_eq_one
    intro v _
    by_cases hb:bitsToAssignment n x u=true ∧ bitsToAssignment n x v=true
    · have he := h u v hb.1 hb.2
      simp [graphEdgePenalty,he]
    · simp [graphEdgePenalty,edgePenalty,hb]
  · rw [if_neg h]
    change ¬ (∀ u v, bitsToAssignment n x u=true → bitsToAssignment n x v=true → G.edge u v=false) at h
    push_neg at h
    obtain ⟨u,v,hu,hv,he⟩ := h
    have ht : G.edge u v=true := Bool.eq_true_of_not_eq_false he
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [graphEdgePenalty,edgePenalty,ht,hu,hv]

/-- Executable ordered list of actual source edges. Each undirected edge appears in both orientations. -/
def orderedEdges {n : ℕ} (G : Complexity.MatrixGraph n) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun u => ((List.finRange n).filter (fun v => G.edge u v)).map (fun v => (u,v)))

 theorem orderedEdges_mem {n : ℕ} (G : Complexity.MatrixGraph n) (e : Fin n × Fin n) :
    e ∈ orderedEdges G ↔ G.edge e.1 e.2=true := by
  rcases e with ⟨u,v⟩
  simp [orderedEdges,List.mem_flatMap,List.mem_filter]

 theorem orderedEdges_ne {n : ℕ} (G : Complexity.MatrixGraph n) (u v : Fin n)
    (h : (u,v) ∈ orderedEdges G) : u≠v := by
  intro he
  subst v
  have hh := (orderedEdges_mem G (u,u)).mp h
  rw [G.loopless u] at hh
  contradiction

 theorem prod_map_filter_bool {α R : Type*} [Monoid R] (w : List α) (p : α → Bool) (f : α → R) :
    ((w.filter p).map f).prod=(w.map (fun a => if p a then f a else 1)).prod := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases h:p a <;> simp [List.filter_cons,h,ih]

theorem prod_flatMap {α R : Type*} [Monoid R] (w : List α) (f : α → List R) :
    (w.flatMap f).prod=(w.map (fun a => (f a).prod)).prod := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [List.flatMap_cons,List.prod_append,ih]

/-- Skipping nonedges in the emitted list preserves the exact product of edge constraints. -/
theorem orderedEdges_penalty_product {n : ℕ} (G : Complexity.MatrixGraph n) (x : CodeBits n) :
    ((orderedEdges G).map (fun e => edgePenalty e.1 e.2 x)).prod =
      ∏ u : Fin n, ∏ v : Fin n, graphEdgePenalty G u v x := by
  unfold orderedEdges
  rw [List.map_flatMap,prod_flatMap]
  simp only [List.map_map,Function.comp_def]
  simp_rw [prod_map_filter_bool]
  simp only [graphEdgePenalty,← List.ofFn_eq_map,List.prod_ofFn]

/-- The concrete emitted edge list has exactly the source-independent assignment semantics. -/
theorem orderedEdges_indicator {n : ℕ} (G : Complexity.MatrixGraph n) (x : CodeBits n) :
    ((orderedEdges G).map (fun e => edgePenalty e.1 e.2 x)).prod =
      if codeIndependent G x then 1 else 0 := by
  rw [orderedEdges_penalty_product,edge_penalty_indicator]

/-- Applying the full list of source constraints between preparation and reset counts genuine independent sets. -/
theorem orderedEdges_counting_sandwich {n : ℕ} (G : Complexity.MatrixGraph n) :
    (preparationMatrix n * Matrix.diagonal (fun x =>
      ((orderedEdges G).map (fun e => edgePenalty e.1 e.2 x)).prod) * resetMatrix n)
      (zeroBits n) (zeroBits n)=G.independentCount := by
  simp_rw [orderedEdges_indicator]
  exact independent_counting_sandwich G

end HiddenCircuits.Circuit
