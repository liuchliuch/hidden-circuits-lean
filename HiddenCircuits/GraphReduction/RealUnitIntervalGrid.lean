import HiddenCircuits.GraphReduction.RealUnitIntervals
import HiddenCircuits.GraphReduction.FiniteOrderRank
import Mathlib.Data.Real.Archimedean

/-!
# Bounded grid models of every finite real unit-interval graph

Rank the finitely many occupied integer parts and their successors, and rank
the fractional parts separately. This preserves every comparison x ≤ y+1,
including equal fractional parts. It compresses arbitrarily separated connected
components at once. This is a mathematical existence/transport construction;
it does not purport to recognize a graph from its adjacency encoding.
-/
namespace HiddenCircuits.GraphReduction.RealUnitInterval.Grid
open FiniteOrderRank
variable {V : Type*} [Fintype V]
noncomputable section

/-- Include each occupied floor and its successor so a missing integer bucket
cannot turn a nonedge into an edge during rank compression. -/
def integerParts (f : V → ℝ) : Finset ℤ :=
  Finset.univ.image (fun v => ⌊f v⌋) ∪ Finset.univ.image (fun v => ⌊f v⌋+1)

def fractionalParts (f : V → ℝ) : Finset ℝ := Finset.univ.image (fun v => Int.fract (f v))

def denominator : ℕ := max 1 (Fintype.card V)

def numerator (f : V → ℝ) (v : V) : ℕ :=
  denominator (V:=V) * rank (integerParts f) ⌊f v⌋ +
    rank (fractionalParts f) (Int.fract (f v))

lemma floor_mem (f : V → ℝ) (v : V) : ⌊f v⌋ ∈ integerParts f := by
  simp [integerParts]
lemma floor_succ_mem (f : V → ℝ) (v : V) : ⌊f v⌋+1 ∈ integerParts f := by
  simp [integerParts]
lemma fract_mem (f : V → ℝ) (v : V) : Int.fract (f v) ∈ fractionalParts f := by
  simp [fractionalParts]
lemma denominator_pos : 0 < denominator (V:=V) := by simp [denominator]
lemma card_le_denominator : Fintype.card V ≤ denominator (V:=V) := le_max_right _ _
lemma integerParts_card (f : V → ℝ) : (integerParts f).card ≤ 2 * Fintype.card V := by
  unfold integerParts
  calc
    _ ≤ (Finset.univ.image (fun v => ⌊f v⌋)).card +
        (Finset.univ.image (fun v => ⌊f v⌋+1)).card := Finset.card_union_le _ _
    _ ≤ Fintype.card V + Fintype.card V := by
      exact Nat.add_le_add (by simpa using Finset.card_image_le (s:=Finset.univ) (f:=fun v => ⌊f v⌋))
        (by simpa using Finset.card_image_le (s:=Finset.univ) (f:=fun v => ⌊f v⌋+1))
    _ = _ := by omega
lemma fractionalParts_card (f : V → ℝ) : (fractionalParts f).card ≤ Fintype.card V := by
  simpa [fractionalParts] using Finset.card_image_le (s:=Finset.univ) (f:=fun v => Int.fract (f v))
lemma fractional_rank_lt (f : V → ℝ) (v : V) :
    rank (fractionalParts f) (Int.fract (f v)) < denominator (V:=V) :=
  (lt_card (fract_mem f v)).trans_le ((fractionalParts_card f).trans card_le_denominator)

/-- Both closed endpoints lie strictly below 2nD; D=n on nonempty inputs. -/
lemma endpoint_bound (f : V → ℝ) (v : V) :
    numerator f v + denominator (V:=V) < 2 * Fintype.card V * denominator (V:=V) := by
  have hi := int_two_le (floor_mem f v) (floor_succ_mem f v)
  have hc := integerParts_card f
  have hf := fractional_rank_lt f v
  unfold numerator
  nlinarith

/-- The grid numerator preserves the exact closed-distance comparison. -/
theorem comparison (f : V → ℝ) (v w : V) :
    numerator f v ≤ numerator f w + denominator (V:=V) ↔ f v ≤ f w + 1 := by
  have hv := fractional_rank_lt f v
  have hw := fractional_rank_lt f w
  have hD := denominator_pos (V:=V)
  have hv0 := Int.fract_nonneg (f v)
  have hw0 := Int.fract_nonneg (f w)
  have hv1 := Int.fract_lt_one (f v)
  have hw1 := Int.fract_lt_one (f w)
  have hev : f v = (⌊f v⌋ : ℝ) + Int.fract (f v) := by unfold Int.fract; ring
  have hew : f w = (⌊f w⌋ : ℝ) + Int.fract (f w) := by unfold Int.fract; ring
  rcases le_or_gt ⌊f v⌋ ⌊f w⌋ with h | h
  · have hg := mono (integerParts f) h
    have hr : (⌊f v⌋ : ℝ) ≤ (⌊f w⌋ : ℝ) := by exact_mod_cast h
    constructor
    · intro _; linarith
    · intro _; unfold numerator; nlinarith
  · by_cases he : ⌊f v⌋ = ⌊f w⌋+1
    · have hg : rank (integerParts f) ⌊f v⌋ = rank (integerParts f) ⌊f w⌋+1 := by
        rw [he,int_succ (floor_mem f w)]
      have hr : (⌊f v⌋ : ℝ) = (⌊f w⌋ : ℝ)+1 := by exact_mod_cast he
      have hc := le_iff (s:=fractionalParts f) (a:=Int.fract (f v)) (fract_mem f w)
      unfold numerator
      rw [hg]
      constructor
      · intro hn
        have hf : rank (fractionalParts f) (Int.fract (f v)) ≤
            rank (fractionalParts f) (Int.fract (f w)) := by nlinarith
        have := hc.mp hf
        linarith
      · intro hn
        have hf : Int.fract (f v) ≤ Int.fract (f w) := by linarith
        have := hc.mpr hf
        nlinarith
    · have hh : ⌊f w⌋+1 < ⌊f v⌋ := by omega
      have hg := strict (floor_succ_mem f w) hh
      rw [int_succ (floor_mem f w)] at hg
      have hr : (⌊f w⌋ : ℝ)+2 ≤ (⌊f v⌋ : ℝ) := by exact_mod_cast (show ⌊f w⌋+2 ≤ ⌊f v⌋ by omega)
      constructor
      · intro hn; unfold numerator at hn; nlinarith
      · intro hn; linarith

end
end HiddenCircuits.GraphReduction.RealUnitInterval.Grid

namespace HiddenCircuits.GraphReduction.RealUnitInterval
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
noncomputable section

/-- Every finite closed real unit-interval model has a bounded integer model.
The positive common length is max(1,n), including the empty graph. -/
def Representation.integerGrid (r : Representation G) : UnitInterval.Representation G where
  length := Grid.denominator (V:=V)
  positive := by exact_mod_cast Grid.denominator_pos (V:=V)
  left v := Grid.numerator r.unitLength.left v
  adjacency v w := by
    rw [r.unitLength.adjacency]
    apply and_congr_right
    intro _
    rw [RealUnitInterval.icc_overlap (by rw [Representation.unitLength_length]; linarith)
      (by rw [Representation.unitLength_length]; linarith)]
    change (r.unitLength.left v ≤ r.unitLength.left w + 1 ∧
      r.unitLength.left w ≤ r.unitLength.left v + 1) ↔ _
    rw [UnitInterval.icc_overlap (by exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      (by exact le_add_of_nonneg_right (Nat.cast_nonneg _))]
    rw [←Grid.comparison r.unitLength.left v w,←Grid.comparison r.unitLength.left w v]
    constructor
    · rintro ⟨hv,hw⟩
      constructor
      · exact_mod_cast hv
      · exact_mod_cast hw
    · rintro ⟨hv,hw⟩
      constructor
      · exact_mod_cast hv
      · exact_mod_cast hw

/-- Dividing the integer model by its common length yields the promised
1/n rational grid whenever n is positive. -/
def Representation.rationalUnitGrid (r : Representation G) : UnitInterval.Representation G :=
  r.integerGrid.unitLength

@[simp] theorem Representation.rationalUnitGrid_length (r : Representation G) :
    r.rationalUnitGrid.length = 1 := rfl

@[simp] theorem Representation.rationalUnitGrid_left (r : Representation G) (v : V) :
    r.rationalUnitGrid.left v =
      (Grid.numerator r.unitLength.left v : ℚ) / Grid.denominator (V:=V) := rfl

/-- Both encoded integer endpoints have quadratic magnitude, without any
connectivity, endpoint distinctness, or generic-position assumption. -/
theorem Representation.integerGrid_endpoint_bound (r : Representation G) (v : V) :
    Grid.numerator r.unitLength.left v + Grid.denominator (V:=V) <
      2 * Fintype.card V * Grid.denominator (V:=V) := Grid.endpoint_bound _ _

/-- For nonempty vertex types the denominator is literally the vertex count. -/
theorem Representation.exists_n_grid (r : Representation G) (hn : 0 < Fintype.card V) :
    ∃ x : V → ℕ,
      (∀ v, x v + Fintype.card V < 2 * (Fintype.card V)^2) ∧
      ∀ v w, G.Adj v w ↔ v ≠ w ∧
        x v ≤ x w + Fintype.card V ∧ x w ≤ x v + Fintype.card V := by
  have hD : Grid.denominator (V:=V) = Fintype.card V := max_eq_right hn
  refine ⟨Grid.numerator r.unitLength.left,?_,?_⟩
  · intro v
    simpa [hD,pow_two,Nat.mul_assoc] using Grid.endpoint_bound r.unitLength.left v
  · intro v w
    rw [r.unitLength.adjacency,RealUnitInterval.icc_overlap
      (by rw [Representation.unitLength_length]; linarith)
      (by rw [Representation.unitLength_length]; linarith)]
    change (v ≠ w ∧ r.unitLength.left v ≤ r.unitLength.left w+1 ∧
      r.unitLength.left w ≤ r.unitLength.left v+1) ↔ _
    rw [←Grid.comparison r.unitLength.left v w,←Grid.comparison r.unitLength.left w v,hD]

/-- Natural real and rational equal-length graph classes coincide on all finite
labeled vertex types. This statement asserts existence, not runtime recognition. -/
theorem graph_iff_rational : UnitIntervalGraph G ↔ Nonempty (UnitInterval.Representation G) := by
  constructor
  · rintro ⟨r⟩
    exact ⟨r.integerGrid⟩
  · rintro ⟨r⟩
    exact ⟨r.toReal⟩

end
end HiddenCircuits.GraphReduction.RealUnitInterval
