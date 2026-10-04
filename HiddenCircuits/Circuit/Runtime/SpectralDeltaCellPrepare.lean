import HiddenCircuits.Circuit.Runtime.SpectralDeltaItems
import HiddenCircuits.Circuit.Runtime.DeltaOracleRuntime
import HiddenCircuits.Circuit.Runtime.SourceSampleSuffix

/-! A physical native Delta query in the fixed source arithmetic register bank. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaCell
open Complexity OracleBlock BinaryArithmetic Polynomial SourceSample SourceQueryRecovery

abbrev clean (acc : ℤ×ℤ) : Values := {accumulator:=acc}
def emitterEmbedding : Fin 16 ↪ Fin 64 where
  toFun i := (![0,2,3,23,24,25,26,27,28,29,30,32,33,34,35,63] : Fin 16→Fin 64) i
  inj' := by decide +kernel
def parserEmbedding : Fin 4 ↪ Fin 64 where
  toFun i := (![63,31,24,25] : Fin 4→Fin 64) i
  inj' := by decide +kernel
noncomputable def emit : OracleBlock 63 := rename SpectralDeltaEmitter.program emitterEmbedding
noncomputable def constants : OracleBlock 63 := seq (prepend 14 (signedBits 1))
  (seq (prepend 18 (signedBits 1)) (prepend 19 (signedBits 1)))
noncomputable def prepare : OracleBlock 63 := seq emit (seq readFirst (seq readSecond constants))
noncomputable def prepareTime : Polynomial ℕ := SpectralDeltaEmitter.time.comp (3*X)+2*SourceSample.readTime+40

def prepared {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) (acc : ℤ×ℤ) : Values where
  accumulator := acc
  geometricNumerator := signedBits 1
  dyadicDenominator := signedBits 1
  dyadicNumerator := signedBits 1
  firstNumerator := signedBits (spectralWeightData (forbidOccurrences w) 0 r.val).1
  secondNumerator := signedBits (spectralWeightData (signOccurrences w) (-1) s.val).1
  query := (SpectralDeltaEmitter.query w r.val s.val).encode

set_option maxHeartbeats 1200000 in
lemma emit_executes (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) (v : Values)
    (hq : v.query=[]) :
    ∃c,emit.Executes g (store (canonical w 0 r s 0) v)
      (store (canonical w 0 r s 0) {v with query:=(SpectralDeltaEmitter.query w r s).encode}) c ∧
      c≤SpectralDeltaEmitter.time.eval ((circuitBits n w).length+r+s) := by
  obtain ⟨c,hc,hb⟩:=SpectralDeltaEmitter.program_executes g w r s
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ emitterEmbedding g hc
  · funext i;fin_cases i <;> simp [emitterEmbedding,store,canonical,SpectralDeltaEmitter.store,hq,Function.comp_def]
  · funext i;fin_cases i <;> simp [emitterEmbedding,store,canonical,SpectralDeltaEmitter.store,Function.comp_def]
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 15 rfl).elim

lemma constants_executes (g : BitString→ℕ) (p : Parameters) (v : Values)
    (h14 : v.geometricNumerator=[]) (h18 : v.dyadicDenominator=[]) (h19 : v.dyadicNumerator=[]) :
    constants.Executes g (store p v)
      (store p {v with geometricNumerator:=signedBits 1,dyadicDenominator:=signedBits 1,dyadicNumerator:=signedBits 1}) 25 := by
  let v1 : Values:={v with geometricNumerator:=signedBits 1}
  let v2 : Values:={v1 with dyadicDenominator:=signedBits 1}
  let v3 : Values:={v2 with dyadicNumerator:=signedBits 1}
  have h1 : (prepend (14:Fin 64) (signedBits 1)).Executes g (store p v) (store p v1) 7 := by
    convert prepend_executes g (14:Fin 64) (signedBits 1) (store p v) using 1
    rw [show store p v 14=[] from h14,List.append_nil,update_geometricNumerator]
  have h2 : (prepend (18:Fin 64) (signedBits 1)).Executes g (store p v1) (store p v2) 7 := by
    convert prepend_executes g (18:Fin 64) (signedBits 1) (store p v1) using 1
    rw [show store p v1 18=[] from h18,List.append_nil,update_dyadicDenominator]
  have h3 : (prepend (19:Fin 64) (signedBits 1)).Executes g (store p v2) (store p v3) 7 := by
    convert prepend_executes g (19:Fin 64) (signedBits 1) (store p v2) using 1
    rw [show store p v2 19=[] from h19,List.append_nil,update_dyadicNumerator]
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)

set_option maxHeartbeats 1200000 in
lemma prepare_executes (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (acc : ℤ×ℤ) (B : ℕ)
    (hB : ∀i,(store (canonical w 0 r.val s.val 0) (clean acc) i).length≤B) :
    ∃c,prepare.Executes g (store (canonical w 0 r.val s.val 0) (clean acc))
      (store (canonical w 0 r.val s.val 0) (prepared w r s acc)) c ∧ c≤prepareTime.eval B := by
  let v0:=clean acc
  let v1 : Values:={v0 with query:=(SpectralDeltaEmitter.query w r.val s.val).encode}
  let v2 : Values:={v1 with firstNumerator:=signedBits (spectralWeightData (forbidOccurrences w) 0 r.val).1}
  let v3 : Values:={v2 with secondNumerator:=signedBits (spectralWeightData (signOccurrences w) (-1) s.val).1}
  obtain ⟨c1,h1,hb1⟩:=emit_executes g w r.val s.val v0 rfl
  obtain ⟨c2,h2,hb2⟩:=readFirst_executes g w 0 r s.val 0 v1 rfl
  obtain ⟨c3,h3,hb3⟩:=readSecond_executes g w 0 r.val s 0 v2 rfl
  have h4:=constants_executes g (canonical w 0 r.val s.val 0) v3 rfl rfl rfl
  have hL : (circuitBits n w).length≤B := hB 0
  have hr : r.val≤B := by simpa [store,canonical] using hB 2
  have hs : s.val≤B := by simpa [store,canonical] using hB 3
  have hf : (SpectralWeightsProgram.numeratorStream (forbidOccurrences w) false).length≤B := hB 7
  have hz : (SpectralWeightsProgram.numeratorStream (signOccurrences w) true).length≤B := hB 8
  have hc1:=hb1.trans (polynomial_nat_eval_mono SpectralDeltaEmitter.time (show (circuitBits n w).length+r.val+s.val≤3*B by omega))
  have hlookup (L j : ℕ) (hL : L≤B) (hj : j≤B) : HiddenCircuits.GraphReduction.Runtime.lookupBound L j≤SourceSample.readTime.eval B := by
    have hm:=Nat.mul_le_mul (show j+1≤B+1 by omega) (show 6*L+14≤6*B+14 by omega)
    simp only [HiddenCircuits.GraphReduction.Runtime.lookupBound,SourceSample.readTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    omega
  have hc2:=hb2.trans (hlookup _ _ hf hr)
  have hc3:=hb3.trans (hlookup _ _ hz hs)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  simp only [prepareTime,eval_add,eval_mul,eval_ofNat,eval_comp,eval_X]
  dsimp only at hc1
  omega

noncomputable def parse : OracleBlock 63 := SamplePairParser.on parserEmbedding
noncomputable def moveDenominator : OracleBlock 63 := moveOn 63 15 24 (by decide) (by decide) (by decide)
noncomputable def call : OracleBlock 63 := seq (query 63 63) (seq parse moveDenominator)
noncomputable def callTime : Polynomial ℕ := 10*DeltaOracleRuntime.time+20
noncomputable def answered {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) (acc : ℤ×ℤ) : Values :=
  {prepared w r s acc with answer:=signedBits ((SpectralDelta.value w r.val s.val).num), geometricDenominator:=signedBits ((SpectralDelta.value w r.val s.val).den:ℤ),query:=[]}

set_option maxHeartbeats 1200000 in
lemma call_executes (g : BitString→ℕ) (hg : DeltaOracle g) {n : ℕ} (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (acc : ℤ×ℤ) :
    ∃c,call.Executes g (store (canonical w 0 r.val s.val 0) (prepared w r s acc))
      (store (canonical w 0 r.val s.val 0) (answered w r s acc)) c ∧
      c≤callTime.eval (SpectralDeltaEmitter.query w r.val s.val).encode.length := by
  let p:=canonical w 0 r.val s.val 0
  let q:=SpectralDelta.value w r.val s.val
  let v:=prepared w r s acc
  let v1 : Values:={v with query:=RationalOracleEncoding.bits q}
  let v2 : Values:={v with query:=signedBits (q.den:ℤ),answer:=signedBits q.num}
  have h1:=DeltaOracleRuntime.query_executes (63:Fin 64) g hg (SpectralDeltaEmitter.query w r.val s.val) (store p v) rfl
  rw [update_query] at h1
  have h2 : parse.Executes g (store p v1) (store p v2) (5*(signedBits q.num).length+7) := by
    apply SamplePairParser.on_executes parserEmbedding g (signedBits q.num) (signedBits (q.den:ℤ))
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  have h3:=moveOn_executes g (63:Fin 64) 15 24 (by decide) (by decide) (by decide) (store p v2) rfl
  change moveDenominator.Executes g (store p v2) (Function.update (Function.update (store p v2) (15:Fin 64) (signedBits (q.den:ℤ)++[])) (63:Fin 64) []) (6*(signedBits (q.den:ℤ)).length+5) at h3
  rw [List.append_nil,update_geometricDenominator,update_query] at h3
  have hbits : 2*(signedBits q.num).length+1+(signedBits (q.den:ℤ)).length=(RationalOracleEncoding.bits q).length := by
    simp [RationalOracleEncoding.bits,pairBits];omega
  have hcost:=DeltaOracleRuntime.query_time (SpectralDeltaEmitter.query w r.val s.val)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  simp only [callTime,eval_add,eval_mul,eval_ofNat]
  change 1+(SpectralDeltaEmitter.query w r.val s.val).encode.length+(RationalOracleEncoding.bits q).length≤_ at hcost
  change 1+(SpectralDeltaEmitter.query w r.val s.val).encode.length+(RationalOracleEncoding.bits q).length+(5*(signedBits q.num).length+7+(6*(signedBits (q.den:ℤ)).length+5)+2)+2≤_
  omega
end HiddenCircuits.Circuit.Runtime.SpectralDeltaCell
