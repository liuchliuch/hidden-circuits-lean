import HiddenCircuits.GraphReduction.UnitIntervalGraphs
import HiddenCircuits.GraphReduction.MonotoneSize
import HiddenCircuits.GraphReduction.CliqueProbeInterpolation

/-! Exact vertex, degree, query, and endpoint-sign bounds for Section 10. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators

 theorem unitOriginal_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) :
    Fintype.card (UnitOriginalVertex p h S T)=4*p*h := by
  rw [Fintype.card_sum,retainedEven_card hh,oddVertex_card]
  ring

 theorem unitOriginal_half_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) :
    Fintype.card (UnitOriginalVertex p h S T)/2=2*p*h := by
  rw [unitOriginal_card hh,show 4*p*h=(2*p*h)*2 by ring,Nat.mul_div_cancel (2*p*h) (by decide)]

 theorem unitIntervalQuery_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) (s : ℕ) :
    Fintype.card (UnitOriginalVertex p h S T ⊕ (Fin (h+1) × Fin s))=4*p*h+(h+1)*s := by
  rw [cliqueProbeGraph_card,unitOriginal_card hh,Fintype.card_fin]

 theorem unitIntervalProbe_degree {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) :
    (cliqueProbePolynomial (unitIntervalOriginalGraph pairs S T) (unitIntervalAttachment S T)).natDegree≤2*p*h := by
  simpa only [unitOriginal_half_card hh] using cliqueProbePolynomial_degree
    (unitIntervalOriginalGraph pairs S T) (unitIntervalAttachment S T)

 theorem unitIntervalProbe_query_count (p h : ℕ) : Fintype.card (Fin (2*p*h+1))=2*p*h+1 :=
  Fintype.card_fin _

/-- The exact Section10 query-size bound, with the single even sample shared by all h+1 probes. -/
theorem unitIntervalProbe_query_size {p h : ℕ} (hh : 0<h) (S T : State (2*p) p)
    (t : Fin (2*p*h+1)) :
    Fintype.card (UnitOriginalVertex p h S T ⊕ (Fin (h+1) × Fin (2*t.val)))≤4*p*h*(h+2) := by
  rw [unitIntervalQuery_card hh]
  have ht : t.val≤2*p*h := by omega
  calc
    4*p*h+(h+1)*(2*t.val) ≤ 4*p*h+(h+1)*(2*(2*p*h)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 ht)) _
    _ = _ := by ring

 theorem oddLayer_shift_sign_product (p h : ℕ) :
    (∏ v : OddVertex (2*p) h, (-1 : ℚ)^(v.1.val+1))=1 := by
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply Finset.prod_eq_one
  intro r _
  rw [pow_mul,pow_two,pairedLayer_first_sign]
  simp

/-- The same fixed sign (-1)^(ph), now flipping the first rather than the second cuts. -/
theorem unitEndpoint_sign {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) :
    (∏ v : UnitOriginalVertex p h S T, unitEndpointSign v)=(-1 : ℚ)^(p*h) := by
  rw [Fintype.prod_sum_type]
  change (∏ x : RetainedEven p h S T, (-1 : ℚ)^x.val.1.val) *
    (∏ y : OddVertex (2*p) h, (-1 : ℚ)^(y.1.val+1)) = _
  rw [oddLayer_shift_sign_product,mul_one]
  have he := monotone_endpoint_sign hh S T
  rw [oddLayer_sign_product,mul_one] at he
  exact he

end HiddenCircuits.GraphReduction
