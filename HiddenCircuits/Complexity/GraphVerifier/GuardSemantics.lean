import HiddenCircuits.Complexity.GraphVerifier.PairScanSemantics
import HiddenCircuits.Complexity.GraphVerifier.TwoParse

/-! Exact length/padding guard, derived bounds, and its connection to the canonical verifier. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime

 def guardValue (xs : BitString) : Bool :=
  let x := (parse xs).left
  let w := (parse xs).right
  let h := (parse x).left
  let p := (parse x).right
  (parse xs).ok && (parse x).ok && h.all id && decide (x.length=w.length) &&
    decide (p.length=h.length*h.length) && (w.drop h.length).all (fun b => !b)

 theorem guard_data_bounds (xs : BitString) :
    (parse (parse xs).left).left.length ≤ xs.length ∧
    (parse (parse xs).left).right.length ≤ xs.length ∧ (parse xs).right.length ≤ xs.length := by
  have h₁ := parse_lengths xs
  have h₂ := parse_lengths (parse xs).left
  omega

 theorem guard_implies_lengths (xs : BitString) (hg : guardValue xs=true) :
    (parse (parse xs).left).right.length=(parse (parse xs).left).left.length*(parse (parse xs).left).left.length ∧
      (parse (parse xs).left).left.length ≤ (parse xs).right.length := by
  simp only [guardValue,Bool.and_eq_true,decide_eq_true_eq] at hg
  have hok : (parse (parse xs).left).ok=true := by tauto
  have hlen : (parse xs).left.length=(parse xs).right.length := by tauto
  have hp : unpairBits (parse xs).left=some ((parse (parse xs).left).left,(parse (parse xs).left).right) := by
    rw [parse_spec,hok]
    rfl
  have hh := unpairBits_length hp
  constructor
  · tauto
  · omega

/-- The guarded finite pair scan accepts exactly the canonical independent-set certificate. -/
theorem verifier_eq_guard_scan (xs : BitString) :
    verifier xs=(guardValue xs && scanPairs (parse (parse xs).left).left.length
      (parse (parse xs).left).right (parse xs).right) := by
  rw [verifier_eq_flat]
  apply Bool.eq_iff_iff.mpr
  simp only [flatVerifier,flatVerifyPair,guardValue,Bool.and_eq_true,decide_eq_true_eq,
    ValidPayload,scanPairs_iff]
  constructor
  · intro h
    have he : (parse xs).left.length=(parse xs).right.length := by tauto
    tauto
  · intro h
    have he : (parse xs).right.length=(parse xs).left.length := by tauto
    tauto

end HiddenCircuits.Complexity.GraphVerifier.Runtime
