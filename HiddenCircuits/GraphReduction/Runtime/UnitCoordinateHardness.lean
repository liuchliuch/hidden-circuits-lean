import HiddenCircuits.GraphReduction.Runtime.SuppliedUnitHardness
import HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitCoordinateWordSolver

/-! Corollary1.3 exact hardness on the interval-coordinate input itself.
No adjacency matrix or matching certificate is supplied to this oracle. -/
namespace HiddenCircuits.GraphReduction
open Complexity Complexity.BinaryArithmetic Runtime.WordGraph

def unitCoordinateBits (G : GraphInput) (R : UnitIntegerRepresentation G) : BitString :=
  encodeBitList (signedBits R.denominator::List.ofFn (fun i => signedBits (R.left i)))

def UnitCoordinateOracle (g : BitString → ℕ) : Prop :=
  ∀ (G : GraphInput) (R : UnitIntegerRepresentation G),g (unitCoordinateBits G R)=perfectMatchingCount G.2.graph

lemma queryUnitCoordinateBits {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    unitCoordinateBits (unitGraphInput (fun i => ps.get i) S T s) (queryUnitRepresentation ps S T s)=
      Runtime.unitRepresentationBits ps S T s := by
  have h := encodeBitList_injective (queryUnitRepresentation_bits ps S T s)
  change [(unitGraphInput (fun i => ps.get i) S T s).encode,
    unitCoordinateBits (unitGraphInput (fun i => ps.get i) S T s) (queryUnitRepresentation ps S T s)]=
      [(unitGraphInput (fun i => ps.get i) S T s).encode,Runtime.unitRepresentationBits ps S T s] at h
  exact (List.cons.inj (List.cons.inj h).2).1

lemma unitCoordinate_wordSolverSpec (g : BitString → ℕ) (hg : UnitCoordinateOracle g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec UnitCoordinateDriver.program g UnitCoordinateDriver.time := by
  intro w
  apply UnitCoordinateDriver.program_executes g w
  intro _ q
  have h := hg (CliqueRecovery.query false w q)
    (queryUnitRepresentation (sampleWord w.word q.1.val) w.source w.target (2*q.2.val))
  change g (unitCoordinateBits (unitGraphInput (fun i => (sampleWord w.word q.1.val).get i) w.source w.target (2*q.2.val))
    (queryUnitRepresentation (sampleWord w.word q.1.val) w.source w.target (2*q.2.val)))=_ at h
  rw [queryUnitCoordinateBits] at h
  exact h

theorem unitCoordinate_counting_sharpPHard (g : BitString → ℕ) (hg : UnitCoordinateOracle g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard UnitCoordinateDriver.program g UnitCoordinateDriver.time (unitCoordinate_wordSolverSpec g hg)
end HiddenCircuits.GraphReduction
