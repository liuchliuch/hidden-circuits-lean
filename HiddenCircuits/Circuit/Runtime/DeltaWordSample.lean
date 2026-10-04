import HiddenCircuits.Circuit.Runtime.DeltaWordRecovery
import HiddenCircuits.Circuit.Runtime.SourceSampleProgram

/-! A single physically generated Delta sample, geometric integer weight and
signed dyadic factor. SourceSample is used only as a finite register layout and
as its already verified elementary arithmetic operations. No spectral loop is
called, and the two spectral factors are the literal integer one. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaWordSample
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceSample DeltaWordRecovery

def canonical {n : ℕ} (w : List (DeltaGate n)) (u : ℕ) : Parameters where
  circuit:=DeltaWordEmitter.circuitBits n w
  normalization:=0
  firstCount:=0
  secondCount:=0
  r:=0
  s:=0
  u:=u
  firstNumerators:=[]
  secondNumerators:=[]
  firstDenominator:=signedBits 1
  secondDenominator:=signedBits 1
noncomputable def sample : OracleBlock 63 := DeltaWordEmitter.on sampleEmbedding
noncomputable def constants : OracleBlock 63 := seq (prepend 20 (signedBits 1)) (prepend 21 (signedBits 1))
noncomputable def beforeCall : OracleBlock 63 := seq geometric (seq sample (seq dyadic constants))
noncomputable def sampleInputSize : Polynomial ℕ := 2*X
noncomputable def scalarInputSize : Polynomial ℕ := 2*X+DeltaWordEmitter.emitTime.comp sampleInputSize
noncomputable def beforeTime : Polynomial ℕ := GeometricFrontend.time+DeltaWordEmitter.time.comp sampleInputSize+
  DyadicScalar.time.comp scalarInputSize+22

set_option maxHeartbeats 1000000 in
lemma sample_executes (g : BitString → ℕ) {n : ℕ} (hn : 0<n) (w : List (DeltaGate n))
    (u : ℕ) (v : Values) (he : v.exponent=[]) (hs : v.negative=[]) (hq : v.query=[]) :
    ∃c,sample.Executes g (store (canonical w u) v)
      (store (canonical w u) {v with exponent:=List.replicate (DeltaWordEmitter.sampleExponent w u) true,negative:=[DeltaWordEmitter.sampleNegative w false],query:=wordBits (compileWordInstance hn
          (w.map (DeltaGate.compileSample u)) (zeroBits n) (zeroBits n))}) c ∧
      c≤DeltaWordEmitter.time.eval (DeltaWordEmitter.inputSize w 0 0 u) := by
  obtain ⟨c,hc,hb⟩:=DeltaWordEmitter.on_executes sampleEmbedding g (store (canonical w u) v) hn w 0 0 u
    (by funext i;fin_cases i <;> simp [store,canonical,sampleEmbedding,SampleEmitter.store,he,hs,hq])
  refine ⟨c,?_,hb⟩
  simpa only [show sampleEmbedding 6=16 from rfl,show sampleEmbedding 7=17 from rfl,show sampleEmbedding 31=63 from rfl,
    update_exponent,update_negative,update_query] using hc

lemma constants_executes (g : BitString→ℕ) (p : Parameters) (v : Values)
    (h1 : v.firstNumerator=[]) (h2 : v.secondNumerator=[]) :
    constants.Executes g (store p v) (store p {v with firstNumerator:=signedBits 1,secondNumerator:=signedBits 1}) 16 := by
  have ha : (prepend (20:Fin 64) (signedBits 1)).Executes g (store p v)
      (store p {v with firstNumerator:=signedBits 1}) 7 := by
    convert prepend_executes g (20:Fin 64) (signedBits 1) (store p v) using 1
    funext i;fin_cases i <;> simp [store,h1]
  have hb : (prepend (21:Fin 64) (signedBits 1)).Executes g (store p {v with firstNumerator:=signedBits 1})
      (store p {v with firstNumerator:=signedBits 1,secondNumerator:=signedBits 1}) 7 := by
    convert prepend_executes g (21:Fin 64) (signedBits 1) (store p {v with firstNumerator:=signedBits 1}) using 1
    funext i;fin_cases i <;> simp [store,h2]
  exact seq_executes _ _ g ha hb

def prepared {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) (acc : ℤ×ℤ) : Values where
  accumulator:=acc
  degree:=degree w
  geometricNumerator:=signedBits (geometricZeroNumerator (degree w) u)
  geometricDenominator:=signedBits (geometricBasisDenominator (degree w) u)
  exponent:=List.replicate (DeltaWordEmitter.sampleExponent w u.val) true
  negative:=[DeltaWordEmitter.sampleNegative w false]
  dyadicDenominator:=signedBits ((2:ℤ)^(DeltaWordEmitter.sampleExponent w u.val))
  dyadicNumerator:=signedBits (DyadicScalar.numerator (DeltaWordEmitter.sampleNegative w false))
  firstNumerator:=signedBits 1
  secondNumerator:=signedBits 1
  query:=wordBits (word hn w u)

set_option maxHeartbeats 1000000 in
theorem beforeCall_executes (g : BitString→ℕ) {n : ℕ} (hn : 0<n) (w : List (DeltaGate n))
    (u : Index w) (acc : ℤ×ℤ) (B : ℕ)
    (hB : ∀i,(store (canonical w u.val) {accumulator:=acc,degree:=degree w} i).length≤B) :
    ∃c,beforeCall.Executes g (store (canonical w u.val) {accumulator:=acc,degree:=degree w})
      (store (canonical w u.val) (prepared hn w u acc)) c ∧ c≤beforeTime.eval B := by
  let p:=canonical w u.val
  let v0 : Values:={accumulator:=acc,degree:=degree w}
  let v1 : Values:={v0 with geometricNumerator:=signedBits (geometricZeroNumerator (degree w) u),geometricDenominator:=signedBits (geometricBasisDenominator (degree w) u)}
  let v2 : Values:={v1 with exponent:=List.replicate (DeltaWordEmitter.sampleExponent w u.val) true,negative:=[DeltaWordEmitter.sampleNegative w false],query:=wordBits (word hn w u)}
  let v3 : Values:={v2 with dyadicDenominator:=signedBits ((2:ℤ)^(DeltaWordEmitter.sampleExponent w u.val)),dyadicNumerator:=signedBits (DyadicScalar.numerator (DeltaWordEmitter.sampleNegative w false))}
  obtain ⟨c1,h1,hb1⟩:=geometric_executes g p v0 u rfl rfl rfl
  obtain ⟨c2,h2,hb2⟩:=sample_executes g hn w u.val v1 rfl rfl rfl
  obtain ⟨c3,h3,hb3⟩:=dyadic_executes g p v2 (DeltaWordEmitter.sampleExponent w u.val)
    (DeltaWordEmitter.sampleNegative w false) rfl rfl rfl rfl
  simp only [show p.normalization=0 from rfl,Nat.mul_zero,Nat.zero_add] at h3 hb3
  have h4:=constants_executes g p v3 rfl rfl
  have hL : (DeltaWordEmitter.circuitBits n w).length≤B := hB 0
  have hu : u.val≤B := by simpa [store,canonical] using hB 4
  have hd : degree w≤B := by simpa [store] using hB 13
  have hinput : DeltaWordEmitter.inputSize w 0 0 u.val≤2*B := by unfold DeltaWordEmitter.inputSize;omega
  have hE:=(DeltaWordEmitter.emitted_length_bound g w 0 0 u.val).2
  have hmE:=polynomial_nat_eval_mono DeltaWordEmitter.emitTime hinput
  dsimp only at hmE
  have hscalar : DeltaWordEmitter.sampleExponent w u.val≤scalarInputSize.eval B := by
    simp only [scalarInputSize,sampleInputSize,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X]
    omega
  have hc1:=hb1.trans (polynomial_nat_eval_mono GeometricFrontend.time hd)
  have hc2:=hb2.trans (polynomial_nat_eval_mono DeltaWordEmitter.time hinput)
  have hc3:=hb3.trans (polynomial_nat_eval_mono DyadicScalar.time hscalar)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  simp only [beforeTime,sampleInputSize,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  dsimp only [p,v0] at hc1 hc2 hc3
  omega
end HiddenCircuits.Circuit.Runtime.DeltaWordSample
