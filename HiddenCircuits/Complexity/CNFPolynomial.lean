import HiddenCircuits.Complexity.CNFGraph
import HiddenCircuits.Complexity.Cloning
import HiddenCircuits.Complexity.Interpolation

/-! Coefficient extraction on the independence polynomial of the concrete CNF
clause graph. -/
namespace HiddenCircuits.Complexity.CNF
open scoped BigOperators
open Polynomial
variable {n m : ℕ} (F : CNF n m)

abbrev AllIndependentSet := Cloning.IndependentSet F.graph

noncomputable def variableSupport (s : F.AllIndependentSet) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ b : Bool, Sum.inl (i,b) ∈ s.val)

noncomputable def clauseSupport (s : F.AllIndependentSet) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun k => Sum.inr k ∈ s.val)

noncomputable def variableCount (s : F.AllIndependentSet) : ℕ := (F.variableSupport s).card
noncomputable def clauseCount (s : F.AllIndependentSet) : ℕ := (F.clauseSupport s).card

lemma variableCount_le (s : F.AllIndependentSet) : F.variableCount s ≤ n := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin n))

lemma clauseCount_le (s : F.AllIndependentSet) : F.clauseCount s ≤ m := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin m))

lemma literal_unique (s : F.AllIndependentSet) (i : Fin n) {b c : Bool}
    (hb : Sum.inl (i,b) ∈ s.val) (hc : Sum.inl (i,c) ∈ s.val) : b = c := by
  by_contra hbc
  have hne : (Sum.inl (i,b) : Vertex (m := m)) ≠ Sum.inl (i,c) := by simpa using hbc
  exact s.property hb hc hne ⟨rfl,hbc⟩

/-- The top x coefficient selects exactly one vertex from each variable pair. -/
theorem variableCount_eq_iff (s : F.AllIndependentSet) :
    F.variableCount s = n ↔ ∀ i : Fin n, ∃! b : Bool, Sum.inl (i,b) ∈ s.val := by
  classical
  have hcard : F.variableCount s = n ↔ ∀ i : Fin n, ∃ b : Bool, Sum.inl (i,b) ∈ s.val := by
    unfold variableCount variableSupport
    simpa using (Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => ∃ b : Bool, Sum.inl (i,b) ∈ s.val))
  rw [hcard]
  constructor
  · intro h i
    obtain ⟨b,hb⟩ := h i
    exact ⟨b,hb,fun c hc => F.literal_unique s i hc hb⟩
  · intro h i
    exact (h i).exists

noncomputable def fullCoefficientEquiv :
    {s : F.AllIndependentSet // F.variableCount s = n} ≃ F.FullIndependentSet where
  toFun s := ⟨s.val.val,s.val.property,(F.variableCount_eq_iff s.val).mp s.property⟩
  invFun s := ⟨⟨s.val,s.property.1⟩,(F.variableCount_eq_iff ⟨s.val,s.property.1⟩).mpr s.property.2⟩
  left_inv s := rfl
  right_inv s := rfl

/-- Extracting the top coefficient is the sum over actual full-variable independent sets. -/
theorem coefficient_full {R : Type*} [Semiring R] (weight : F.AllIndependentSet → R) :
    (∑ s : F.AllIndependentSet, monomial (F.variableCount s) (weight s)).coeff n =
    ∑ s : F.FullIndependentSet, weight ⟨s.val,s.property.1⟩ := by
  classical
  simp only [finset_sum_coeff,coeff_monomial]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun s : F.AllIndependentSet => F.variableCount s = n) _ (by simp)]
  exact Fintype.sum_equiv F.fullCoefficientEquiv _ _ (fun _ => rfl)

/-- Independence polynomial in the variable activity, after fixing clause activity. -/
noncomputable def columnPolynomial (y : ℚ) : ℚ[X] :=
  ∑ s : F.AllIndependentSet, monomial (F.variableCount s) (y ^ F.clauseCount s)

/-- Independence polynomial in the clause activity, after fixing variable activity. -/
noncomputable def rowPolynomial (x : ℚ) : ℚ[X] :=
  ∑ s : F.AllIndependentSet, monomial (F.clauseCount s) (x ^ F.variableCount s)

lemma columnPolynomial_degree (y : ℚ) : (F.columnPolynomial y).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro s _
  exact (natDegree_monomial_le _).trans (F.variableCount_le s)

lemma rowPolynomial_degree (x : ℚ) : (F.rowPolynomial x).natDegree ≤ m := by
  apply natDegree_sum_le_of_forall_le
  intro s _
  exact (natDegree_monomial_le _).trans (F.clauseCount_le s)

lemma polynomial_cross (x y : ℚ) :
    (F.rowPolynomial x).eval y = (F.columnPolynomial y).eval x := by
  simp only [rowPolynomial,columnPolynomial,eval_finset_sum,eval_monomial]
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

noncomputable def clauseSign (s : F.AllIndependentSet) : ℤ := by
  classical
  exact ∏ k : Fin m, if Sum.inr k ∈ s.val then (-1 : ℤ) else 1

lemma clauseSign_eq_power (s : F.AllIndependentSet) :
    F.clauseSign s = (-1)^F.clauseCount s := by
  classical
  unfold clauseSign
  rw [← Finset.prod_filter]
  simp [clauseCount,clauseSupport]

/-- The wanted coefficient of the signed independence polynomial is exactly #SAT. -/
theorem column_minus_one_coeff :
    (F.columnPolynomial (-1)).coeff n = (F.satCount : ℚ) := by
  rw [columnPolynomial,F.coefficient_full]
  have h := F.satCount_eq_signedFullIndependentCount
  change (F.satCount : ℤ) = ∑ s : F.FullIndependentSet, F.clauseSign ⟨s.val,s.property.1⟩ at h
  simp_rw [F.clauseSign_eq_power] at h
  exact_mod_cast h.symm

/-- Algebraic recovery from a rectangular grid of nonnegative integer activities.
The next bridge replaces each activity value by its unweighted clone count. -/
theorem satCount_grid_recovery :
    recoverGrid n m n (fun i j =>
      (F.rowPolynomial (interpolationNode i)).eval (interpolationNode j)) = (F.satCount : ℚ) := by
  rw [recoverGrid_correct n m n F.rowPolynomial (F.columnPolynomial (-1))
    F.rowPolynomial_degree (F.columnPolynomial_degree (-1))
    (fun x => F.polynomial_cross x (-1)), F.column_minus_one_coeff]

end HiddenCircuits.Complexity.CNF
