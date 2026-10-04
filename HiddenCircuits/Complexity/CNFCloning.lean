import HiddenCircuits.Complexity.CNFPolynomial

/-! Exact arbitrary-CNF recovery from ordinary, unweighted independent-set oracle
queries. This module proves the mathematical query identity; a verified binary
oracle-machine implementation is a separate remaining obligation. -/
namespace HiddenCircuits.Complexity.CNF
open scoped BigOperators
open Polynomial
attribute [local instance] Classical.propDecidable
variable {n m : ℕ} (F : CNF n m)

lemma variableSupport_mem (s : F.AllIndependentSet) (i : F.variableSupport s) :
    ∃ b : Bool, Sum.inl (i.val,b) ∈ s.val :=
  (Finset.mem_filter.mp i.property).2

noncomputable def chosenLiteral (s : F.AllIndependentSet) (i : F.variableSupport s) : Bool :=
  (F.variableSupport_mem s i).choose

lemma chosenLiteral_mem (s : F.AllIndependentSet) (i : F.variableSupport s) :
    Sum.inl (i.val,F.chosenLiteral s i) ∈ s.val := (F.variableSupport_mem s i).choose_spec

noncomputable def selectedVertexEquiv (s : F.AllIndependentSet) :
    s.val ≃ (F.variableSupport s) ⊕ (F.clauseSupport s) where
  toFun v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl ab => exact Sum.inl ⟨ab.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab.2,hv⟩⟩
    | inr k => exact Sum.inr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩
  invFun v := match v with
    | .inl i => ⟨Sum.inl (i.val,F.chosenLiteral s i),F.chosenLiteral_mem s i⟩
    | .inr k => ⟨Sum.inr k.val,(Finset.mem_filter.mp k.property).2⟩
  left_inv v := by
    rcases v with ⟨v,hv⟩
    apply Subtype.ext
    cases v with
    | inl a =>
      rcases a with ⟨i,b⟩
      simp only
      congr 2
      exact F.literal_unique s i (F.chosenLiteral_mem s
        ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hv⟩⟩) hv
    | inr k => rfl
  right_inv v := by
    cases v <;> rfl

/-- Activity is constant on variable vertices and constant on clause vertices. -/
def cloneMultiplicity (a b : ℕ) : Vertex (n := n) (m := m) → ℕ
  | .inl _ => a
  | .inr _ => b

lemma product_cloneMultiplicity (s : F.AllIndependentSet) (a b : ℕ) :
    (∏ v : s.val, cloneMultiplicity a b v.val) =
      a ^ F.variableCount s * b ^ F.clauseCount s := by
  classical
  calc
    _ = ∏ v : (F.variableSupport s) ⊕ (F.clauseSupport s),
        Sum.elim (fun _ => a) (fun _ => b) v := by
      apply Fintype.prod_equiv (F.selectedVertexEquiv s)
      intro v
      rcases v with ⟨v,hv⟩
      cases v <;> rfl
    _ = _ := by simp [Fintype.prod_sum_type,variableCount,clauseCount]

def cloneGraph (a b : ℕ) := Cloning.graph F.graph (cloneMultiplicity a b)

noncomputable def cloneCount (a b : ℕ) : ℕ :=
  Fintype.card (Cloning.IndependentSet (F.cloneGraph a b))

/-- Each query is an ordinary total independent-set count on an unweighted graph. -/
theorem rowPolynomial_eval_cloneCount (a b : ℕ) :
    (F.rowPolynomial (a : ℚ)).eval (b : ℚ) = (F.cloneCount a b : ℚ) := by
  unfold cloneCount cloneGraph
  rw [Cloning.independent_count]
  simp only [rowPolynomial,eval_finset_sum,eval_monomial,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [F.product_cloneMultiplicity]
  push_cast
  rfl

/-- Unconditional exact query identity from #SAT to all-independent-set counting.
No fixed-size counting oracle is assumed. -/
theorem satCount_from_independent_counts :
    recoverGrid n m n (fun i j => (F.cloneCount i.val j.val : ℚ)) = (F.satCount : ℚ) := by
  have h := F.satCount_grid_recovery
  simp only [interpolationNode,F.rowPolynomial_eval_cloneCount] at h
  exact h

/-- Exact vertex count of every emitted unweighted query. -/
theorem cloneGraph_vertex_count (a b : ℕ) :
    Fintype.card (Cloning.Vertex (cloneMultiplicity (n := n) (m := m) a b)) =
      2*n*a+m*b := by
  rw [Cloning.vertex_count]
  simp only [Fintype.sum_sum_type,cloneMultiplicity,Finset.sum_const,Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,smul_eq_mul]
  ring

/-- On the interpolation grid, query graphs have a quadratic vertex bound. -/
theorem cloneGraph_grid_vertex_bound (i : Fin (n+1)) (j : Fin (m+1)) :
    Fintype.card (Cloning.Vertex (cloneMultiplicity (n := n) (m := m) i.val j.val)) ≤
      (2*n+m)^2 := by
  rw [cloneGraph_vertex_count]
  have hi := interpolation_node_bound i
  have hj := interpolation_node_bound j
  have ha := Nat.mul_le_mul_left (2*n) hi
  have hb := Nat.mul_le_mul_left m hj
  nlinarith

end HiddenCircuits.Complexity.CNF
