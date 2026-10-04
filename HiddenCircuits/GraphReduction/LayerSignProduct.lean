import HiddenCircuits.GraphReduction.WeightedGauge

/-! Exact endpoint-sign products for the paired independent layers. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Full odd layers have even width, so their endpoint-sign product is one. -/
theorem oddLayer_sign_product (p h : ℕ) :
    (∏ v : Fin h × Fin (2*p), (-1 : ℚ)^v.1.val) = 1 := by
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply Finset.prod_eq_one
  intro r _
  rw [pow_mul,pow_two,pairedLayer_first_sign]
  simp

/-- Only the last retained even layer contributes a nontrivial global sign.
The first has exponent zero and every internal layer has even width. -/
theorem retainedEven_sign_product (p h : ℕ) (K : Fin (h+1) → Fin (2*p) → Prop)
    (hlast : Fintype.card {x // K (Fin.last h) x} = p)
    (hmid : ∀ r : Fin (h+1), r.val≠0 → r.val≠h → Fintype.card {x // K r x}=2*p) :
    (∏ v : {v : Fin (h+1) × Fin (2*p) // K v.1 v.2}, (-1 : ℚ)^v.val.1.val) =
      (-1 : ℚ)^(p*h) := by
  classical
  rw [← (Equiv.subtypeProdEquivSigmaSubtype K).symm.prod_comp]
  change (∏ v : Σ r : Fin (h+1), {x // K r x}, (-1 : ℚ)^v.1.val) = _
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const,Finset.card_univ]
  rw [Finset.prod_eq_single (Fin.last h)]
  · rw [hlast,← pow_mul]
    congr 1
    simp only [Fin.val_last]
    ring
  · intro r _ hr
    by_cases hzero : r.val=0
    · simp [hzero]
    · have hne : r.val≠h := by
        intro he
        apply hr
        exact Fin.ext (he.trans (Fin.val_last h).symm)
      rw [hmid r hzero hne,pow_mul,pow_two,pairedLayer_first_sign]
      simp
  · simp

end HiddenCircuits.GraphReduction
