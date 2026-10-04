import HiddenCircuits.GraphReduction.Runtime.SignedScan
import HiddenCircuits.GraphReduction.Runtime.UnitCorrectionCallback

/-! Instantiate the literal signed scan with the concrete record
lookup, parser, comparison gates, and cleanup callback. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitSignedScan
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

def edge (second : Bool) (width : ℕ) (records : List VertexRecord) (i j : ℕ) : Bool × Bool :=
  let x := (records[i]?).getD defaultRecord
  let y := (records[j]?).getD defaultRecord
  (decide (unitCorrectionValue second width x y=1),decide (unitCorrectionValue second width x y=-1))

noncomputable def program (second : Bool) : OracleBlock 95 := SignedScan.program (UnitSignedCallback.program second)
noncomputable def bound (n L width C : ℕ) : ℕ :=
  n*(UnitSignedCallback.bound n L width+SignedCounter.timePolynomial.eval (SignedCounter.counterBound C n)+7)+6*n+8

 theorem program_executes (second : Bool) (width height : ℕ) (records : List VertexRecord)
    (g : BitString → ℕ) (i : ℕ) (out outer : BitString) (R : Fin 7 → ℤ) (C : ℕ)
    (hR : Bounded C R) (h1 : R 5=1) (hn : R 6=-1) (hi:i<records.length) :
    ∃ t, (program second).Executes g
      (SignedScan.state records.length i 0 [] out [] outer
        (UnitSignedCallback.params width height (encodeBitList (records.map encodeVertex))) R)
      (SignedScan.state records.length i 0 [] out [] outer
        (UnitSignedCallback.params width height (encodeBitList (records.map encodeVertex)))
        (Function.update R 2 (R 2+SignedScan.total (edge second width records) i 0 records.length))) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length width C := by
  apply SignedScan.program_executes (UnitSignedCallback.program second) (edge second width records)
    records.length (UnitSignedCallback.bound records.length (encodeBitList (records.map encodeVertex)).length width)
    (UnitSignedCallback.params width height (encodeBitList (records.map encodeVertex)))
    ?_ g i out outer R C hR h1 hn hi
  intro g i j out inner outer R hi hj
  simpa only [edge,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some]
    using UnitSignedCallback.program_executes second width height records g i j out inner outer R hi hj

lemma program_queryFree (second : Bool) : (program second).QueryFree :=
  SignedScan.program_queryFree _ (UnitSignedCallback.program_queryFree second)
end HiddenCircuits.GraphReduction.Runtime.UnitSignedScan
