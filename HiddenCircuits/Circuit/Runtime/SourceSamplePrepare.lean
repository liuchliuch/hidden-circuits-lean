import HiddenCircuits.Circuit.Runtime.SourceSampleFrame

/-! Concrete framed execution of the source sample's
metadata, geometric weights, physical query, dyadic scalar, and coefficient reads. -/
namespace HiddenCircuits.Circuit.Runtime.SourceSample
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery

noncomputable def dimensions : OracleBlock 63 := SampleDimensions.on dimensionsEmbedding
noncomputable def geometric : OracleBlock 63 := GeometricFrontend.on geometricEmbedding
noncomputable def sample : OracleBlock 63 := SampleEmitter.on sampleEmbedding
noncomputable def dyadic : OracleBlock 63 := DyadicScalar.on dyadicEmbedding
noncomputable def readFirst : OracleBlock 63 := HiddenCircuits.DH.Runtime.WordArray.readOn firstReadEmbedding
noncomputable def readSecond : OracleBlock 63 := HiddenCircuits.DH.Runtime.WordArray.readOn secondReadEmbedding

set_option maxHeartbeats 800000 in
lemma dimensions_executes (g : BitString → ℕ) (p : Parameters) (v : Values) (hd : v.degree=0) :
    ∃c,dimensions.Executes g (store p v)
      (store p {v with degree:=4*p.r*p.firstCount+4*p.s*p.secondCount}) c ∧
      c≤SampleDimensions.time.eval (p.firstCount+p.secondCount+p.r+p.s) := by
  obtain ⟨c,hc,hb⟩:=SampleDimensions.on_executes dimensionsEmbedding g (store p v) p.firstCount p.secondCount p.r p.s
    (by funext i;fin_cases i <;> simp [store,dimensionsEmbedding,SampleDimensions.store,hd])
  refine ⟨c,?_,hb⟩
  simpa only [show dimensionsEmbedding 6=13 from rfl,update_degree] using hc

set_option maxHeartbeats 800000 in
lemma geometric_executes (g : BitString → ℕ) (p : Parameters) (v : Values) (i : Fin (v.degree+1))
    (hu : p.u=i.val) (hn : v.geometricNumerator=[]) (hd : v.geometricDenominator=[]) :
    ∃c,geometric.Executes g (store p v)
      (store p {v with geometricNumerator:=signedBits (geometricZeroNumerator v.degree i), geometricDenominator:=signedBits (geometricBasisDenominator v.degree i)}) c ∧ c≤GeometricFrontend.time.eval v.degree := by
  obtain ⟨c,hc,hb⟩:=GeometricFrontend.on_executes geometricEmbedding g (store p v) v.degree i
    (by funext j;fin_cases j <;> simp [store,geometricEmbedding,GeometricFrontend.store,hu,hn,hd])
  refine ⟨c,?_,hb⟩
  simpa only [show geometricEmbedding 2=14 from rfl,show geometricEmbedding 3=15 from rfl,
    update_geometricNumerator,update_geometricDenominator] using hc

set_option maxHeartbeats 1000000 in
lemma sample_executes (g : BitString → ℕ) {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (a r s u : ℕ) (v : Values) (he : v.exponent=[]) (hs : v.negative=[]) (hq : v.query=[]) :
    ∃c,sample.Executes g (store (canonical w a r s u) v)
      (store (canonical w a r s u) {v with exponent:=List.replicate (SampleScalar.sampleExponent w r s u) true, negative:=[SampleEmitter.sampleNegative w false],query:=wordBits (compileWordInstance hn ((sampledConstraintCircuit w r s).map (DeltaGate.compileSample u)) (zeroBits n) (zeroBits n))}) c ∧
      c≤SampleEmitter.time.eval (SampleEmitter.inputSize w r s u) := by
  obtain ⟨c,hc,hb⟩:=SampleEmitter.on_executes sampleEmbedding g (store (canonical w a r s u) v) hn w r s u
    (by funext i;fin_cases i <;> simp [store,canonical,sampleEmbedding,SampleEmitter.store,he,hs,hq])
  refine ⟨c,?_,hb⟩
  simpa only [show sampleEmbedding 6=16 from rfl,show sampleEmbedding 7=17 from rfl,show sampleEmbedding 31=63 from rfl,
    update_exponent,update_negative,update_query] using hc

set_option maxHeartbeats 800000 in
lemma dyadic_executes (g : BitString → ℕ) (p : Parameters) (v : Values) (e : ℕ) (negative : Bool)
    (he : v.exponent=List.replicate e true) (hs : v.negative=[negative])
    (hd : v.dyadicDenominator=[]) (hn : v.dyadicNumerator=[]) :
    ∃c,dyadic.Executes g (store p v)
      (store p {v with dyadicDenominator:=signedBits ((2:ℤ)^(3*p.normalization+e)), dyadicNumerator:=signedBits (DyadicScalar.numerator negative)}) c ∧ c≤DyadicScalar.time.eval (p.normalization+e) := by
  obtain ⟨c,hc,hb⟩:=DyadicScalar.on_executes dyadicEmbedding g (store p v) p.normalization e negative
    (by funext i;fin_cases i <;> simp [store,dyadicEmbedding,DyadicScalar.store,he,hs,hd,hn])
  refine ⟨c,?_,hb⟩
  simpa only [show dyadicEmbedding 3=18 from rfl,show dyadicEmbedding 4=19 from rfl,
    update_dyadicDenominator,update_dyadicNumerator] using hc

lemma first_word {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) :
    (((SpectralWeights.vector (forbidOccurrences w) (SpectralTargets.base false) (spectralIndices (forbidOccurrences w))).map signedBits)[r.val]?.getD [])=
      signedBits (spectralWeightData (forbidOccurrences w) 0 r.val).1 := by
  rw [List.getElem?_eq_getElem (by simp),Option.getD_some,List.getElem_map,SpectralWeightsProgram.output_numerator]
  rfl
lemma second_word {n : ℕ} (w : List (ConstraintGate n)) (s : SecondIndex w) :
    (((SpectralWeights.vector (signOccurrences w) (SpectralTargets.base true) (spectralIndices (signOccurrences w))).map signedBits)[s.val]?.getD [])=
      signedBits (spectralWeightData (signOccurrences w) (-1) s.val).1 := by
  rw [List.getElem?_eq_getElem (by simp),Option.getD_some,List.getElem_map,SpectralWeightsProgram.output_numerator]
  rfl
set_option maxHeartbeats 800000 in
lemma readFirst_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n))
    (a : ℕ) (r : FirstIndex w) (s u : ℕ) (v : Values) (hv : v.firstNumerator=[]) :
    ∃c,readFirst.Executes g (store (canonical w a r.val s u) v)
      (store (canonical w a r.val s u) {v with firstNumerator:=signedBits (spectralWeightData (forbidOccurrences w) 0 r.val).1}) c ∧
      c≤HiddenCircuits.GraphReduction.Runtime.lookupBound (SpectralWeightsProgram.numeratorStream (forbidOccurrences w) false).length r.val := by
  obtain ⟨c,hc,hb⟩:=HiddenCircuits.DH.Runtime.WordArray.readOn_executes firstReadEmbedding g
    (store (canonical w a r.val s u) v)
    ((SpectralWeights.vector (forbidOccurrences w) (SpectralTargets.base false) (spectralIndices (forbidOccurrences w))).map signedBits) r.val
    (by funext i;fin_cases i <;> simp [store,canonical,firstReadEmbedding,HiddenCircuits.DH.Runtime.WordArray.store,
      HiddenCircuits.DH.Runtime.WordArray.state,SpectralWeightsProgram.numeratorStream,hv])
  rw [first_word w r] at hc
  refine ⟨c,?_,hb⟩
  simpa only [show firstReadEmbedding 2=20 from rfl,update_firstNumerator] using hc

set_option maxHeartbeats 800000 in
lemma readSecond_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n))
    (a r : ℕ) (s : SecondIndex w) (u : ℕ) (v : Values) (hv : v.secondNumerator=[]) :
    ∃c,readSecond.Executes g (store (canonical w a r s.val u) v)
      (store (canonical w a r s.val u) {v with secondNumerator:=signedBits (spectralWeightData (signOccurrences w) (-1) s.val).1}) c ∧
      c≤HiddenCircuits.GraphReduction.Runtime.lookupBound (SpectralWeightsProgram.numeratorStream (signOccurrences w) true).length s.val := by
  obtain ⟨c,hc,hb⟩:=HiddenCircuits.DH.Runtime.WordArray.readOn_executes secondReadEmbedding g
    (store (canonical w a r s.val u) v)
    ((SpectralWeights.vector (signOccurrences w) (SpectralTargets.base true) (spectralIndices (signOccurrences w))).map signedBits) s.val
    (by funext i;fin_cases i <;> simp [store,canonical,secondReadEmbedding,HiddenCircuits.DH.Runtime.WordArray.store,
      HiddenCircuits.DH.Runtime.WordArray.state,SpectralWeightsProgram.numeratorStream,hv])
  rw [second_word w s] at hc
  refine ⟨c,?_,hb⟩
  simpa only [show secondReadEmbedding 2=21 from rfl,update_secondNumerator] using hc
end HiddenCircuits.Circuit.Runtime.SourceSample
