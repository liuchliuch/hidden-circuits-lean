import HiddenCircuits.GraphReduction.Runtime.UnitRepresentationEmitter

/-! Closed natural-coefficient polynomials for the actual endpoint
encoder, including signed arithmetic, both record scans, and output reversal. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRepresentation
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine Polynomial

noncomputable def inputPolynomial : Polynomial ℕ := X+X+X+X+1002
noncomputable def magnitudePolynomial : Polynomial ℕ := X+X+X+X+X+1002
noncomputable def lookupPolynomial : Polynomial ℕ := 5*X+5*X+(X+1)*(6*X+14)+9
noncomputable def registerPolynomial : Polynomial ℕ := C (2^16)*(inputPolynomial+3)
noncomputable def callbackPolynomial : Polynomial ℕ := 2*lookupPolynomial+3000*X+1000*X+10000
noncomputable def baselinePolynomial : Polynomial ℕ :=
  lookupPolynomial+5*X+100*(magnitudePolynomial+1)^2+100*magnitudePolynomial+
    UnitBaseline.timePolynomial.comp inputPolynomial+4000
noncomputable def scanPolynomial (R : Polynomial ℕ) : Polynomial ℕ :=
  X*(callbackPolynomial+SignedCounter.timePolynomial.comp (R+X+3)+7)+6*X+8
noncomputable def rowPolynomial : Polynomial ℕ :=
  baselinePolynomial+scanPolynomial registerPolynomial+
    scanPolynomial (registerPolynomial+X+3)+10
noncomputable def sizePolynomial : Polynomial ℕ := registerPolynomial+X+3+X+3
noncomputable def bodyPolynomial : Polynomial ℕ := rowPolynomial+12*sizePolynomial+33
noncomputable def headerPolynomial : Polynomial ℕ :=
  100*(X+X+1003)^2+UnitBaseline.timePolynomial.comp (X+X+1002)+
    20*(C (2^16)*(X+X+1005))+10000
noncomputable def prefixPolynomial : Polynomial ℕ := headerPolynomial+5*X+X*(bodyPolynomial+2)+7
noncomputable def timePolynomial : Polynomial ℕ := 3*prefixPolynomial+2*X+X+6

lemma inputPolynomial_eval (M : ℕ) :
    inputPolynomial.eval M=UnitBaseline.inputBound M M (UnitCoordinateRow.maxRecord M) := by
  simp [inputPolynomial,UnitBaseline.inputBound,UnitCoordinateRow.maxRecord]
lemma magnitudePolynomial_eval (M : ℕ) :
    magnitudePolynomial.eval M=UnitBaselineSetup.magnitude M M (UnitCoordinateRow.maxRecord M) := by
  simp [magnitudePolynomial,UnitBaselineSetup.magnitude,UnitCoordinateRow.maxRecord]
lemma lookupPolynomial_eval (M : ℕ) : lookupPolynomial.eval M=lookupBound M M := by
  simp [lookupPolynomial,lookupBound]
lemma registerPolynomial_eval (M : ℕ) :
    registerPolynomial.eval M=UnitCoordinateRow.registerBound M M (UnitCoordinateRow.maxRecord M) := by
  simp [registerPolynomial,inputPolynomial_eval,UnitCoordinateRow.registerBound]
lemma callbackPolynomial_eval (M : ℕ) : callbackPolynomial.eval M=UnitSignedCallback.bound M M M := by
  simp [callbackPolynomial,lookupPolynomial_eval,UnitSignedCallback.bound]
lemma baselinePolynomial_eval (M : ℕ) :
    baselinePolynomial.eval M=UnitBaselineRow.bound M M M M (UnitCoordinateRow.maxRecord M) := by
  simp [baselinePolynomial,lookupPolynomial_eval,magnitudePolynomial_eval,inputPolynomial_eval,UnitBaselineRow.bound]
lemma scanPolynomial_eval (R : Polynomial ℕ) (M : ℕ) :
    (scanPolynomial R).eval M=UnitSignedScan.bound M M M (R.eval M) := by
  simp [scanPolynomial,callbackPolynomial_eval,UnitSignedScan.bound,SignedCounter.counterBound]
lemma rowPolynomial_eval (M : ℕ) : rowPolynomial.eval M=UnitCoordinateRow.uniformRowBound M := by
  simp [rowPolynomial,scanPolynomial_eval,registerPolynomial_eval,baselinePolynomial_eval,
    UnitCoordinateRow.uniformRowBound,UnitCoordinateRow.bound,SignedCounter.counterBound]
lemma sizePolynomial_eval (M : ℕ) : sizePolynomial.eval M=UnitCoordinateRow.uniformSizeBound M := by
  simp [sizePolynomial,registerPolynomial_eval,UnitCoordinateRow.uniformSizeBound,
    UnitCoordinateRow.resultBound,SignedCounter.counterBound]
lemma bodyPolynomial_eval (M : ℕ) : bodyPolynomial.eval M=UnitCoordinateRows.bodyBound M := by
  simp [bodyPolynomial,rowPolynomial_eval,sizePolynomial_eval,UnitCoordinateRows.bodyBound]
lemma headerPolynomial_eval (M : ℕ) : headerPolynomial.eval M=UnitLengthHeader.bound M M := by
  simp [headerPolynomial,UnitLengthHeader.bound]

lemma header_bound_mono {width height M : ℕ} (hw:width≤M) (hh:height≤M) :
    UnitLengthHeader.bound width height≤headerPolynomial.eval M := by
  rw [headerPolynomial_eval]
  have hp := polynomial_nat_eval_mono UnitBaseline.timePolynomial (show width+height+1002≤M+M+1002 by omega)
  unfold UnitLengthHeader.bound
  gcongr

lemma prefix_bound (width height : ℕ) (records : List VertexRecord) :
    prefixBound width height records≤prefixPolynomial.eval (UnitCoordinateRows.size width height records) := by
  let M := UnitCoordinateRows.size width height records
  have hn : records.length≤M := by dsimp [M,UnitCoordinateRows.size];omega
  have hw : width≤M := by dsimp [M,UnitCoordinateRows.size];omega
  have hh : height≤M := by dsimp [M,UnitCoordinateRows.size];omega
  have hheader := header_bound_mono hw hh
  change prefixBound width height records≤prefixPolynomial.eval M
  simp only [prefixPolynomial,eval_add,eval_mul,eval_X,eval_ofNat,bodyPolynomial_eval]
  unfold prefixBound
  change UnitLengthHeader.bound width height+5*records.length+
    records.length*(UnitCoordinateRows.bodyBound M+2)+7≤_
  gcongr

lemma bound_polynomial (width height : ℕ) (records : List VertexRecord) :
    bound width height records≤timePolynomial.eval (UnitCoordinateRows.size width height records) := by
  have hp := prefix_bound width height records
  have hn : records.length≤UnitCoordinateRows.size width height records := by
    unfold UnitCoordinateRows.size;omega
  simp only [timePolynomial,eval_add,eval_mul,eval_X,eval_ofNat]
  unfold bound
  omega

 theorem program_polynomial (width height : ℕ) (records : List VertexRecord) (g : BitString → ℕ) :
    ∃ t, program.Executes g (initial width height records) (finalState width height records) t ∧
      t≤timePolynomial.eval (records.length+(encodeBitList (records.map encodeVertex)).length+width+height) := by
  obtain ⟨t,ht,hb⟩ := program_executes width height records g
  exact ⟨t,ht,hb.trans (bound_polynomial width height records)⟩

end HiddenCircuits.GraphReduction.Runtime.UnitRepresentation
