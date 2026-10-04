import HiddenCircuits.GraphReduction.Runtime.CliqueHardness
import HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitWordSolver

/-! Actual hardness with a supplied rational unit-interval representation.
The coordinates are integer numerators and one positive shared denominator;
labels are retained even when coordinate values repeat. -/
namespace HiddenCircuits.GraphReduction
open Complexity Complexity.BinaryArithmetic
open Runtime.WordGraph

structure UnitIntegerRepresentation (G : GraphInput) where
  denominator : ℤ
  positive : 0<denominator
  left : Fin G.1 → ℤ
  adjacency : ∀i j,G.2.graph.Adj i j ↔ i≠j ∧
    (Set.Icc ((left i:ℚ)/denominator) ((left i:ℚ)/denominator+1) ∩
      Set.Icc ((left j:ℚ)/denominator) ((left j:ℚ)/denominator+1)).Nonempty

def suppliedUnitBits (G : GraphInput) (R : UnitIntegerRepresentation G) : BitString :=
  encodeBitList [G.encode,encodeBitList (signedBits R.denominator::List.ofFn (fun i => signedBits (R.left i)))]

def SuppliedUnitOracle (g : BitString → ℕ) : Prop :=
  ∀ (G : GraphInput) (R : UnitIntegerRepresentation G),g (suppliedUnitBits G R)=perfectMatchingCount G.2.graph

def queryUnitRepresentation {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    UnitIntegerRepresentation (unitGraphInput (fun i => ps.get i) S T s) where
  denominator := UnitInterval.commonLength (2*p) ps.length
  positive := commonLength_positive _ _
  left := Runtime.unitLeftInteger ps S T s
  adjacency := Runtime.unitRepresentation_adjacency ps S T s

lemma queryUnitRepresentation_bits {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    suppliedUnitBits (unitGraphInput (fun i => ps.get i) S T s) (queryUnitRepresentation ps S T s)=
      Runtime.UnitSuppliedQuery.bits ps S T s := by
  have he : List.ofFn (fun i : Fin (unitGraphInput (fun i => ps.get i) S T s).1 =>
      signedBits (Runtime.unitLeftInteger ps S T s i))=
      (unitEnumeration S T s).labels.map (fun v => signedBits (unitQueryLeftInteger ps v)) := by
    have h := congrArg (List.map (fun v => signedBits (unitQueryLeftInteger ps v)))
      (List.ofFn_get (unitEnumeration S T s).labels)
    simpa only [List.map_ofFn,Function.comp_def,Runtime.unitLeftInteger] using h
  unfold suppliedUnitBits queryUnitRepresentation Runtime.UnitSuppliedQuery.bits Runtime.unitRepresentationBits
  rw [he]

lemma suppliedUnit_wordSolverSpec (g : BitString → ℕ) (hg : SuppliedUnitOracle g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec UnitDriver.program g UnitDriver.time := by
  intro w
  apply UnitDriver.program_executes g w
  intro _ q
  have h := hg (CliqueRecovery.query false w q)
    (queryUnitRepresentation (sampleWord w.word q.1.val) w.source w.target (2*q.2.val))
  change g (suppliedUnitBits (unitGraphInput (fun i => (sampleWord w.word q.1.val).get i) w.source w.target (2*q.2.val))
    (queryUnitRepresentation (sampleWord w.word q.1.val) w.source w.target (2*q.2.val)))=_ at h
  rw [queryUnitRepresentation_bits] at h
  exact h

theorem suppliedUnit_matching_sharpPHard (g : BitString → ℕ) (hg : SuppliedUnitOracle g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard UnitDriver.program g UnitDriver.time (suppliedUnit_wordSolverSpec g hg)
end HiddenCircuits.GraphReduction
