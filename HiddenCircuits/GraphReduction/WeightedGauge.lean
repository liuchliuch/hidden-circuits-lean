import HiddenCircuits.GraphReduction.WeightedExpansion

/-! Endpoint-sign gauge identities for the actual bipartite matching sum. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def edgeIndicator (R : X → Y → Prop) (x : X) (y : Y) : ℚ := by
  classical
  exact if R x y then 1 else 0

/-- A zero-one weighted matching sum is the actual simple-unweighted graph count. -/
theorem weightedBipartiteCount_indicator (R : X → Y → Prop) :
    weightedBipartiteCount (edgeIndicator R) = (perfectMatchingCount (cutGraph R) : ℚ) := by
  classical
  rw [cutPerfectMatchingCount]
  simp [weightedBipartiteCount,edgeIndicator,Fintype.prod_boole,CutBijection,Fintype.card_subtype]

/-- Multiplying an edge by its two endpoint weights contributes a fixed factor to every
perfect matching, since its bijection uses every original vertex exactly once. -/
theorem weightedBipartiteCount_gauge (w : X → Y → ℚ) (a : X → ℚ) (b : Y → ℚ) :
    weightedBipartiteCount (fun x y => a x * w x y * b y) =
      (∏ x, a x) * (∏ y, b y) * weightedBipartiteCount w := by
  classical
  unfold weightedBipartiteCount
  simp_rw [Finset.prod_mul_distrib]
  have hb (e : X ≃ Y) : (∏ x, b (e x)) = ∏ y, b y := e.prod_comp b
  simp_rw [hb]
  calc
    ∑ e : X ≃ Y, (∏ x, a x) * (∏ x, w x (e x)) * (∏ y, b y) =
        ∑ e : X ≃ Y, ((∏ x, a x) * (∏ y, b y)) * (∏ x, w x (e x)) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := (Finset.mul_sum ..).symm

/-- The fixed sign of the target matching sum follows from endpoint parity alone. -/
theorem weightedBipartiteCount_signed_graph (R : X → Y → Prop) (a : X → ℚ) (b : Y → ℚ) :
    weightedBipartiteCount (fun x y => a x * edgeIndicator R x y * b y) =
      (∏ x, a x) * (∏ y, b y) * (perfectMatchingCount (cutGraph R) : ℚ) := by
  rw [weightedBipartiteCount_gauge,weightedBipartiteCount_indicator]

/-- Integer layer ranks give the signed second cuts in Section 9. -/
theorem pairedLayer_first_sign (r : ℕ) : (-1 : ℚ)^r * (-1 : ℚ)^r = 1 := by
  rw [← pow_two,← pow_mul]
  simp [Nat.mul_comm r 2,pow_mul]

 theorem pairedLayer_second_sign (r : ℕ) : (-1 : ℚ)^(r+1) * (-1 : ℚ)^r = -1 := by
  rw [pow_succ]
  calc
    (-1 : ℚ)^r * -1 * (-1 : ℚ)^r = -(((-1 : ℚ)^r) * ((-1 : ℚ)^r)) := by ring
    _ = -1 := by rw [pairedLayer_first_sign]

end HiddenCircuits.GraphReduction
