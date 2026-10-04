import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateBounds

namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRow
open Complexity Complexity.BinaryArithmetic RegisterMachine

lemma scanBound_mono {n L width C n' L' width' C' : ℕ} (hn:n≤n') (hL:L≤L') (hw:width≤width') (hC:C≤C') :
    UnitSignedScan.bound n L width C≤UnitSignedScan.bound n' L' width' C' := by
  have hp := polynomial_nat_eval_mono SignedCounter.timePolynomial
    (show SignedCounter.counterBound C n≤SignedCounter.counterBound C' n' by unfold SignedCounter.counterBound;omega)
  unfold UnitSignedScan.bound UnitSignedCallback.bound lookupBound
  gcongr

def maxRecord (M : ℕ) : VertexRecord := {defaultRecord with layer:=M,track:=M,cut:={defaultRecord.cut with index:=M}}
noncomputable def uniformRowBound (M : ℕ) : ℕ := bound M M M M (maxRecord M)
noncomputable def uniformSizeBound (M : ℕ) : ℕ := resultBound M M M (maxRecord M)

 theorem uniform_bound (n L width height : ℕ) (x : VertexRecord) (M : ℕ)
    (hn:n≤M) (hL:L≤M) (hw:width≤M) (hh:height≤M)
    (hlayer:x.layer≤M) (htrack:x.track≤M) (hindex:x.cut.index≤M) :
    bound n L width height x≤uniformRowBound M ∧ resultBound width height n x≤uniformSizeBound M := by
  have hi : UnitBaseline.inputBound width height x≤UnitBaseline.inputBound M M (maxRecord M) := by
    dsimp [UnitBaseline.inputBound,maxRecord];omega
  have hm : UnitBaselineSetup.magnitude width height x≤UnitBaselineSetup.magnitude M M (maxRecord M) := by
    dsimp [UnitBaselineSetup.magnitude,maxRecord];omega
  have hb : registerBound width height x≤registerBound M M (maxRecord M) := by unfold registerBound;omega
  have hc : SignedCounter.counterBound (registerBound width height x) n≤SignedCounter.counterBound (registerBound M M (maxRecord M)) M := by
    unfold SignedCounter.counterBound;omega
  have hbase : UnitBaselineRow.bound n L width height x≤UnitBaselineRow.bound M M M M (maxRecord M) := by
    have hp := polynomial_nat_eval_mono UnitBaseline.timePolynomial hi
    unfold UnitBaselineRow.bound lookupBound
    gcongr
  have hs1 := scanBound_mono hn hL hw hb
  have hs2 := scanBound_mono hn hL hw hc
  constructor
  · dsimp only [uniformRowBound,bound]
    omega
  · dsimp only [uniformSizeBound,resultBound,SignedCounter.counterBound]
    omega

 theorem record_uniform (width height : ℕ) (records : List VertexRecord) (i : Fin records.length) :
    bound records.length (encodeBitList (records.map encodeVertex)).length width height (records.get i)≤
        uniformRowBound (records.length+(encodeBitList (records.map encodeVertex)).length+width+height) ∧
      resultBound width height records.length (records.get i)≤
        uniformSizeBound (records.length+(encodeBitList (records.map encodeVertex)).length+width+height) := by
  have h := descriptor_record_length records i
  rw [encodeVertex_length] at h
  apply uniform_bound <;> omega

end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRow
