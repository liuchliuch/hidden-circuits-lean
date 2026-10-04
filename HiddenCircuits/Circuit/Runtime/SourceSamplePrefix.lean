import HiddenCircuits.Circuit.Runtime.SourceSamplePrepare

/-! The complete actual pre-query source sample pipeline,
with a polynomial cost in the initial maximum physical stack length. -/
namespace HiddenCircuits.Circuit.Runtime.SourceSample
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery

noncomputable def beforeCall : OracleBlock 63 := seq geometric (seq sample (seq dyadic (seq readFirst readSecond)))
noncomputable def readTime : Polynomial ℕ := 10*X+(X+1)*(6*X+14)+9
noncomputable def sampleInputSize : Polynomial ℕ := 4*X
noncomputable def scalarInputSize : Polynomial ℕ := 5*X+SampleEmitter.emitTime.comp sampleInputSize
noncomputable def beforeTime : Polynomial ℕ := GeometricFrontend.time+SampleEmitter.time.comp sampleInputSize+
  DyadicScalar.time.comp scalarInputSize+2*readTime+8

def prepared {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) (acc : ℤ×ℤ) : Values where
  accumulator := acc
  degree := degree w r.val s.val
  geometricNumerator := signedBits (geometricZeroNumerator (degree w r.val s.val) u)
  geometricDenominator := signedBits (geometricBasisDenominator (degree w r.val s.val) u)
  exponent := List.replicate (SampleScalar.sampleExponent w r.val s.val u.val) true
  negative := [SampleEmitter.sampleNegative w false]
  dyadicDenominator := signedBits ((2:ℤ)^(3*a+SampleScalar.sampleExponent w r.val s.val u.val))
  dyadicNumerator := signedBits (DyadicScalar.numerator (SampleEmitter.sampleNegative w false))
  firstNumerator := signedBits (spectralWeightData (forbidOccurrences w) 0 r.val).1
  secondNumerator := signedBits (spectralWeightData (signOccurrences w) (-1) s.val).1
  query := wordBits (word hn w r s u)

set_option maxHeartbeats 1000000 in
theorem beforeCall_executes (g : BitString → ℕ) {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) (acc : ℤ×ℤ) (B : ℕ)
    (hB : ∀i,(store (canonical w a r.val s.val u.val) {accumulator:=acc,degree:=degree w r.val s.val} i).length≤B) :
    ∃c,beforeCall.Executes g (store (canonical w a r.val s.val u.val) {accumulator:=acc,degree:=degree w r.val s.val})
      (store (canonical w a r.val s.val u.val) (prepared hn w a r s u acc)) c ∧ c≤beforeTime.eval B := by
  let p:=canonical w a r.val s.val u.val
  let v0 : Values:={accumulator:=acc,degree:=degree w r.val s.val}
  let v1 : Values:={v0 with geometricNumerator:=signedBits (geometricZeroNumerator (degree w r.val s.val) u),geometricDenominator:=signedBits (geometricBasisDenominator (degree w r.val s.val) u)}
  let v2 : Values:={v1 with exponent:=List.replicate (SampleScalar.sampleExponent w r.val s.val u.val) true,negative:=[SampleEmitter.sampleNegative w false],query:=wordBits (word hn w r s u)}
  let v3 : Values:={v2 with dyadicDenominator:=signedBits ((2:ℤ)^(3*a+SampleScalar.sampleExponent w r.val s.val u.val)),dyadicNumerator:=signedBits (DyadicScalar.numerator (SampleEmitter.sampleNegative w false))}
  let v4 : Values:={v3 with firstNumerator:=signedBits (spectralWeightData (forbidOccurrences w) 0 r.val).1}
  obtain ⟨c1,h1,hb1⟩:=geometric_executes g p v0 u rfl rfl rfl
  obtain ⟨c2,h2,hb2⟩:=sample_executes g hn w a r.val s.val u.val v1 rfl rfl rfl
  obtain ⟨c3,h3,hb3⟩:=dyadic_executes g p v2 (SampleScalar.sampleExponent w r.val s.val u.val)
    (SampleEmitter.sampleNegative w false) rfl rfl rfl rfl
  obtain ⟨c4,h4,hb4⟩:=readFirst_executes g w a r s.val u.val v3 rfl
  obtain ⟨c5,h5,hb5⟩:=readSecond_executes g w a r.val s u.val v4 rfl
  have hL : (circuitBits n w).length≤B := hB 0
  have ha : a≤B := by simpa [store,canonical] using hB 1
  have hr : r.val≤B := by simpa [store,canonical] using hB 2
  have hs : s.val≤B := by simpa [store,canonical] using hB 3
  have hu : u.val≤B := by simpa [store,canonical] using hB 4
  have hd : degree w r.val s.val≤B := by simpa [store] using hB 13
  have hf : (SpectralWeightsProgram.numeratorStream (forbidOccurrences w) false).length≤B := hB 7
  have hz : (SpectralWeightsProgram.numeratorStream (signOccurrences w) true).length≤B := hB 8
  have hinput : SampleEmitter.inputSize w r.val s.val u.val≤4*B := by unfold SampleEmitter.inputSize;omega
  have hE:=(SampleEmitter.emitted_length_bound g w r.val s.val u.val).2
  have hmE:=polynomial_nat_eval_mono SampleEmitter.emitTime hinput
  dsimp only at hmE
  have hscalar : a+SampleScalar.sampleExponent w r.val s.val u.val≤scalarInputSize.eval B := by
    simp only [scalarInputSize,sampleInputSize,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X]
    omega
  have hc1:=hb1.trans (polynomial_nat_eval_mono GeometricFrontend.time hd)
  have hc2:=hb2.trans (polynomial_nat_eval_mono SampleEmitter.time hinput)
  have hc3:=hb3.trans (polynomial_nat_eval_mono DyadicScalar.time hscalar)
  have hlookup (L j : ℕ) (hL : L≤B) (hj : j≤B) : HiddenCircuits.GraphReduction.Runtime.lookupBound L j≤readTime.eval B := by
    have hm:=Nat.mul_le_mul (show j+1≤B+1 by omega) (show 6*L+14≤6*B+14 by omega)
    simp only [HiddenCircuits.GraphReduction.Runtime.lookupBound,readTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    omega
  have hc4:=hb4.trans (hlookup _ _ hf hr)
  have hc5:=hb5.trans (hlookup _ _ hz hs)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  simp only [beforeTime,sampleInputSize,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  dsimp only [p,v0] at hc1 hc2 hc3
  omega
end HiddenCircuits.Circuit.Runtime.SourceSample
