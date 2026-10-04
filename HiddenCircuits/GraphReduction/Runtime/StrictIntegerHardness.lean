import HiddenCircuits.GraphReduction.Runtime.StrictIntegerMembership
import HiddenCircuits.GraphReduction.Runtime.WordGraph.StrictIntegerWordSolver

/-! Exact machine-grounded completeness for Corollary `cor:integer`. The actual
oracle receives a positive integer radius and a list of labelled integer
coordinates, and its edge relation is |x_i-x_j| < r. -/
namespace HiddenCircuits.GraphReduction
open Complexity Complexity.BinaryArithmetic Runtime.WordGraph

/-- Integer closed intervals of length d give the identical strict-distance
labelled graph at radius d+1, including at the equality boundary. -/
def StrictIntegerRepresentation.ofUnit (G : GraphInput) (R : UnitIntegerRepresentation G) :
    StrictIntegerRepresentation G where
  radius := R.denominator+1
  positive := by have h:=R.positive;omega
  coordinate := R.left
  adjacency i j := by
    rw [R.adjacency,Runtime.CoordinateGraph.integer_intervals _ _ _ R.positive]
    apply and_congr_right
    intro _
    rw [abs_lt]
    omega

lemma strictInteger_header_translation (G : GraphInput) (R : UnitIntegerRepresentation G) :
    Runtime.StrictIntegerHeader.bits false (unitCoordinateBits G R)=
      strictIntegerBits G (StrictIntegerRepresentation.ofUnit G R) := by
  simp only [unitCoordinateBits,Runtime.StrictIntegerHeader.bits_encode,Runtime.StrictIntegerHeader.delta,
    Bool.false_eq_true,if_false,strictIntegerBits,StrictIntegerRepresentation.ofUnit]

lemma strictInteger_wordSolverSpec (g : BitString → ℕ) (hg : StrictIntegerOracle g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec StrictIntegerDriver.program g StrictIntegerDriver.time := by
  intro w
  apply StrictIntegerDriver.program_executes g w
  intro _ q
  have h := hg (CliqueRecovery.query false w q)
    (StrictIntegerRepresentation.ofUnit _
      (queryUnitRepresentation (sampleWord w.word q.1.val) w.source w.target (2*q.2.val)))
  rw [←strictInteger_header_translation] at h
  change g (Runtime.StrictIntegerHeader.bits false
    (unitCoordinateBits (unitGraphInput (fun i=>(sampleWord w.word q.1.val).get i)
      w.source w.target (2*q.2.val))
      (queryUnitRepresentation (sampleWord w.word q.1.val) w.source w.target (2*q.2.val))))=_ at h
  rw [queryUnitCoordinateBits] at h
  exact h

/-- The only assumption is the target counting-oracle contract. All coordinate
emission, radius conversion, source translation and arithmetic run in the
proved finite-stack oracle machine, in polynomial bit time. -/
theorem strictInteger_counting_sharpPHard (g : BitString → ℕ) (hg : StrictIntegerOracle g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard StrictIntegerDriver.program g StrictIntegerDriver.time
    (strictInteger_wordSolverSpec g hg)

theorem strictIntegerProblem_sharpPHard : SharpPHard strictIntegerProblem :=
  strictInteger_counting_sharpPHard strictIntegerProblem strictIntegerProblem_oracle

/-- Literal strict-positive-integer-radius completeness, with a fully specified
total extension to raw strings and no supplied runtime/compiler assumptions. -/
theorem strictInteger_sharpP_complete :
    SharpP strictIntegerProblem ∧SharpPHard strictIntegerProblem ∧StrictIntegerOracle strictIntegerProblem :=
  ⟨strictIntegerProblem_sharpP,strictIntegerProblem_sharpPHard,strictIntegerProblem_oracle⟩
end HiddenCircuits.GraphReduction
