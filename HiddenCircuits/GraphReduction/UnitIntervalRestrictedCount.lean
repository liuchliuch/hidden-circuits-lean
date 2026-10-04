import HiddenCircuits.GraphReduction.UnitIntervalRecognition
import HiddenCircuits.GraphReduction.RealUnitIntervalsHardness

/-! The literal zero-on-reject totalization of unit-interval matching counting.
Its semantic agreement and unconditional hardness are proved here. Its #P
membership still requires the separate charged binary recognition runtime; the
promise-class #P theorem is not misrepresented as proving that stronger claim. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalRecognition
open Complexity

noncomputable def restrictedProblem (xs : BitString) : ℕ :=
  match GraphInput.decode xs with
  | none => 0
  | some G => if (recognize G.2.graph).isSome then perfectMatchingCount G.2.graph else 0

lemma restrictedProblem_on_class (G : GraphInput)
    (h : RealUnitInterval.UnitIntervalGraph G.2.graph) :
    restrictedProblem G.encode = perfectMatchingCount G.2.graph := by
  have ha := (recognize_iff G.2.graph).mpr h
  simp [restrictedProblem,ha]

lemma restrictedProblem_off_class (G : GraphInput)
    (h : ¬RealUnitInterval.UnitIntervalGraph G.2.graph) : restrictedProblem G.encode = 0 := by
  have ha : (recognize G.2.graph).isSome = false :=
    Bool.eq_false_iff.mpr (fun ht => h ((recognize_iff G.2.graph).mp ht))
  simp [restrictedProblem,ha]

lemma restrictedProblem_malformed {xs : BitString} (h : GraphInput.decode xs = none) :
    restrictedProblem xs = 0 := by simp [restrictedProblem,h]

/-- This particular, fully specified zero-on-reject function is #P-hard,
by the already machine-grounded graph-only reduction. -/
theorem restrictedProblem_sharpPHard : SharpPHard restrictedProblem :=
  realUnit_matching_sharpPHard _ restrictedProblem_on_class

end HiddenCircuits.GraphReduction.UnitIntervalRecognition
