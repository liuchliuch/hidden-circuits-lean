import HiddenCircuits.GraphReduction.RealUnitIntervals
import HiddenCircuits.GraphReduction.FiniteOrderRank
import Mathlib.Data.Real.Archimedean

/-!
# Executable bounded-grid compression of rational unit-interval models

Rank the finitely many occupied integer parts and their successors, and rank
the fractional parts separately. This preserves every comparison x ≤ y+1,
including equal fractional parts. It compresses arbitrarily separated connected
components at once. All coordinate comparisons and floor operations are rational and executable.
This module is coordinate compression, not a graph recognizer.
-/
namespace HiddenCircuits.GraphReduction.UnitInterval.RationalGrid
open FiniteOrderRank
variable {V : Type*} [Fintype V]

/-- Include each occupied floor and its successor so a missing integer bucket
cannot turn a nonedge into an edge during rank compression. -/
def integerParts (f : V → ℚ) : Finset ℤ :=
  Finset.univ.image (fun v => ⌊f v⌋) ∪ Finset.univ.image (fun v => ⌊f v⌋+1)

def fractionalParts (f : V → ℚ) : Finset ℚ := Finset.univ.image (fun v => Int.fract (f v))

def denominator : ℕ := max 1 (Fintype.card V)

def numerator (f : V → ℚ) (v : V) : ℕ :=
  denominator (V:=V) * rank (integerParts f) ⌊f v⌋ +
    rank (fractionalParts f) (Int.fract (f v))

lemma floor_mem (f : V → ℚ) (v : V) : ⌊f v⌋ ∈ integerParts f := by
  simp [integerParts]
lemma floor_succ_mem (f : V → ℚ) (v : V) : ⌊f v⌋+1 ∈ integerParts f := by
  simp [integerParts]
lemma fract_mem (f : V → ℚ) (v : V) : Int.fract (f v) ∈ fractionalParts f := by
  simp [fractionalParts]
lemma denominator_pos : 0 < denominator (V:=V) := by simp [denominator]
lemma card_le_denominator : Fintype.card V ≤ denominator (V:=V) := le_max_right _ _
lemma integerParts_card (f : V → ℚ) : (integerParts f).card ≤ 2 * Fintype.card V := by
  unfold integerParts
  calc
    _ ≤ (Finset.univ.image (fun v => ⌊f v⌋)).card +
        (Finset.univ.image (fun v => ⌊f v⌋+1)).card := Finset.card_union_le _ _
    _ ≤ Fintype.card V + Fintype.card V := by
      exact Nat.add_le_add (by simpa using Finset.card_image_le (s:=Finset.univ) (f:=fun v => ⌊f v⌋))
        (by simpa using Finset.card_image_le (s:=Finset.univ) (f:=fun v => ⌊f v⌋+1))
    _ = _ := by omega
lemma fractionalParts_card (f : V → ℚ) : (fractionalParts f).card ≤ Fintype.card V := by
  simpa [fractionalParts] using Finset.card_image_le (s:=Finset.univ) (f:=fun v => Int.fract (f v))
lemma fractional_rank_lt (f : V → ℚ) (v : V) :
    rank (fractionalParts f) (Int.fract (f v)) < denominator (V:=V) :=
  (lt_card (fract_mem f v)).trans_le ((fractionalParts_card f).trans card_le_denominator)

/-- Both closed endpoints lie strictly below 2nD; D=n on nonempty inputs. -/
lemma endpoint_bound (f : V → ℚ) (v : V) :
    numerator f v + denominator (V:=V) < 2 * Fintype.card V * denominator (V:=V) := by
  have hi := int_two_le (floor_mem f v) (floor_succ_mem f v)
  have hc := integerParts_card f
  have hf := fractional_rank_lt f v
  unfold numerator
  nlinarith

/-- The grid numerator preserves the exact closed-distance comparison. -/
theorem comparison (f : V → ℚ) (v w : V) :
    numerator f v ≤ numerator f w + denominator (V:=V) ↔ f v ≤ f w + 1 := by
  have hv := fractional_rank_lt f v
  have hw := fractional_rank_lt f w
  have hD := denominator_pos (V:=V)
  have hv0 := Int.fract_nonneg (f v)
  have hw0 := Int.fract_nonneg (f w)
  have hv1 := Int.fract_lt_one (f v)
  have hw1 := Int.fract_lt_one (f w)
  have hev : f v = (⌊f v⌋ : ℚ) + Int.fract (f v) := by unfold Int.fract; ring
  have hew : f w = (⌊f w⌋ : ℚ) + Int.fract (f w) := by unfold Int.fract; ring
  rcases le_or_gt ⌊f v⌋ ⌊f w⌋ with h | h
  · have hg := mono (integerParts f) h
    have hr : (⌊f v⌋ : ℚ) ≤ (⌊f w⌋ : ℚ) := by exact_mod_cast h
    constructor
    · intro _; linarith
    · intro _; unfold numerator; nlinarith
  · by_cases he : ⌊f v⌋ = ⌊f w⌋+1
    · have hg : rank (integerParts f) ⌊f v⌋ = rank (integerParts f) ⌊f w⌋+1 := by
        rw [he,int_succ (floor_mem f w)]
      have hr : (⌊f v⌋ : ℚ) = (⌊f w⌋ : ℚ)+1 := by exact_mod_cast he
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
      have hr : (⌊f w⌋ : ℚ)+2 ≤ (⌊f v⌋ : ℚ) := by exact_mod_cast (show ⌊f w⌋+2 ≤ ⌊f v⌋ by omega)
      constructor
      · intro hn; unfold numerator at hn; nlinarith
      · intro hn; linarith

end HiddenCircuits.GraphReduction.UnitInterval.RationalGrid

namespace HiddenCircuits.GraphReduction.UnitInterval
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Executable bounded integer compression of a rational interval model. -/
def Representation.integerGrid (r : Representation G) : Representation G where
  length := RationalGrid.denominator (V:=V)
  positive := by exact_mod_cast RationalGrid.denominator_pos (V:=V)
  left v := RationalGrid.numerator r.unitLength.left v
  adjacency v w := by
    rw [r.unitLength.adjacency]
    apply and_congr_right
    intro _
    rw [icc_overlap (by change r.unitLength.left v ≤ r.unitLength.left v+1; linarith)
      (by change r.unitLength.left w ≤ r.unitLength.left w+1; linarith)]
    change (r.unitLength.left v ≤ r.unitLength.left w+1 ∧
      r.unitLength.left w ≤ r.unitLength.left v+1) ↔ _
    rw [icc_overlap (le_add_of_nonneg_right (Nat.cast_nonneg _))
      (le_add_of_nonneg_right (Nat.cast_nonneg _)),
      ←RationalGrid.comparison r.unitLength.left v w,←RationalGrid.comparison r.unitLength.left w v]
    constructor
    · rintro ⟨hv,hw⟩
      exact ⟨by exact_mod_cast hv,by exact_mod_cast hw⟩
    · rintro ⟨hv,hw⟩
      exact ⟨by exact_mod_cast hv,by exact_mod_cast hw⟩

/-- Output endpoints have quadratic magnitude independent of input magnitudes. -/
lemma Representation.integerGrid_bound (r : Representation G) (v : V) :
    RationalGrid.numerator r.unitLength.left v + RationalGrid.denominator (V:=V) <
      2 * Fintype.card V * RationalGrid.denominator (V:=V) := RationalGrid.endpoint_bound _ _

end HiddenCircuits.GraphReduction.UnitInterval
