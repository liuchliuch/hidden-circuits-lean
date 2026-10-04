import HiddenCircuits.GraphReduction.UnitIntervalMaskedRecognition

/-! Original-n loop clocks suffice for every alive-mask component scan. Extra
fuel after termination leaves the entire semantic state unchanged. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalMaskedScan
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma choose_mem (A S R : Finset V) {v : V} (h : choose G A S R = some v) : v ∈ R :=
  (Finset.mem_sort _).mp (List.argmax_mem h)

@[simp] lemma run_empty (A : Finset V) (fuel : ℕ) (ls : List V) : run G A fuel ls ∅ = (ls,∅) := by
  cases fuel <;> simp [run,choose]

/-- Any fuel above the initial remaining-set size is sufficient and gives
exactly the same output list and remaining mask. -/
theorem run_padding (A : Finset V) (fuel extra : ℕ) (ls : List V) (R : Finset V)
    (hf : R.card ≤ fuel) : run G A (fuel+extra) ls R = run G A fuel ls R := by
  induction fuel generalizing ls R with
  | zero =>
    have he : R=∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hf)
    simp [he]
  | succ fuel ih =>
    rw [Nat.succ_add]
    simp only [run]
    split
    · rfl
    · rename_i y hy
      split
      · rfl
      · apply ih
        rw [Finset.card_erase_of_mem (choose_mem G A ls.toFinset R hy)]
        omega

/-- Specialized fixed original-vertex-count clock used by the bit machine. -/
theorem run_original_clock (A : Finset V) (ls : List V) (R : Finset V)
    (hR : R ⊆ A) :
    run G A (Fintype.card V) ls R = run G A A.card ls R := by
  have hA : A.card ≤ Fintype.card V := Finset.card_le_univ _
  have hh := run_padding G A A.card (Fintype.card V-A.card) ls R (Finset.card_le_card hR)
  simpa only [Nat.add_sub_of_le hA] using hh

end HiddenCircuits.GraphReduction.UnitIntervalMaskedScan

namespace HiddenCircuits.GraphReduction.UnitIntervalMaskedRecognition
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
lemma component_original_clock (A : Finset V) (root : V) :
    component G A root =
      (UnitIntervalMaskedScan.run G A (Fintype.card V) [root] (A.erase root)).1 := by
  rw [UnitIntervalMaskedScan.run_original_clock G A [root] (A.erase root) (Finset.erase_subset _ _)]
  rfl
end HiddenCircuits.GraphReduction.UnitIntervalMaskedRecognition
