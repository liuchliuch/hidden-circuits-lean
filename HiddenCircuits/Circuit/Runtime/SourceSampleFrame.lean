import HiddenCircuits.Circuit.Runtime.SampleGridBounds
import HiddenCircuits.Circuit.Runtime.SourceSpectralSetup
import HiddenCircuits.Circuit.Runtime.GeometricFrontend
import HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulatorRuntime
import HiddenCircuits.DH.Runtime.WordArray

/-! The fixed source driver bank and every finite component
embedding. Semantic values are used only to state actual execution endpoints. -/
namespace HiddenCircuits.Circuit.Runtime.SourceSample
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic

structure Parameters where
  circuit : BitString
  normalization : ℕ
  firstCount : ℕ
  secondCount : ℕ
  r : ℕ
  s : ℕ
  u : ℕ
  firstNumerators : BitString
  secondNumerators : BitString
  firstDenominator : BitString
  secondDenominator : BitString

structure Values where
  accumulator : ℤ×ℤ := (0,1)
  degree : ℕ := 0
  geometricNumerator : BitString := []
  geometricDenominator : BitString := []
  exponent : BitString := []
  negative : BitString := []
  dyadicDenominator : BitString := []
  dyadicNumerator : BitString := []
  firstNumerator : BitString := []
  secondNumerator : BitString := []
  itemDenominator : BitString := []
  answer : BitString := []
  query : BitString := []

def store (p : Parameters) (v : Values) : Store 63 := fun i =>
  if i.val=0 then p.circuit else if i.val=1 then List.replicate p.normalization true
  else if i.val=2 then List.replicate p.r true else if i.val=3 then List.replicate p.s true
  else if i.val=4 then List.replicate p.u true else if i.val=5 then List.replicate p.firstCount true
  else if i.val=6 then List.replicate p.secondCount true else if i.val=7 then p.firstNumerators
  else if i.val=8 then p.secondNumerators else if i.val=9 then p.firstDenominator
  else if i.val=10 then p.secondDenominator else if i.val=11 then signedBits v.accumulator.1
  else if i.val=12 then signedBits v.accumulator.2 else if i.val=13 then List.replicate v.degree true
  else if i.val=14 then v.geometricNumerator else if i.val=15 then v.geometricDenominator
  else if i.val=16 then v.exponent else if i.val=17 then v.negative else if i.val=18 then v.dyadicDenominator
  else if i.val=19 then v.dyadicNumerator else if i.val=20 then v.firstNumerator
  else if i.val=21 then v.secondNumerator else if i.val=22 then v.itemDenominator
  else if i.val=31 then v.answer else if i.val=55 ∨ i.val=56 ∨ i.val=57 then signedBits 0
  else if i.val=63 then v.query else []

def canonical {n : ℕ} (w : List (ConstraintGate n)) (a r s u : ℕ) : Parameters where
  circuit := circuitBits n w
  normalization := a
  firstCount := forbidOccurrences w
  secondCount := signOccurrences w
  r := r
  s := s
  u := u
  firstNumerators := SpectralWeightsProgram.numeratorStream (forbidOccurrences w) false
  secondNumerators := SpectralWeightsProgram.numeratorStream (signOccurrences w) true
  firstDenominator := signedBits (SpectralWeights.denominator (forbidOccurrences w))
  secondDenominator := signedBits (SpectralWeights.denominator (signOccurrences w))

def sampleEmbedding : Fin 32 ↪ Fin 64 where
  toFun i := (![0,2,3,4,23,24,16,17,25,26,27,28,29,30,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,63] : Fin 32→Fin 64) i
  inj' := by decide +kernel
def geometricEmbedding : Fin 25 ↪ Fin 64 where
  toFun i := (![24,25,14,15,26,27,28,29,30,32,33,34,35,36,37,38,39,40,41,42,43,44,45,13,4] : Fin 25→Fin 64) i
  inj' := by decide +kernel
def dyadicEmbedding : Fin 7 ↪ Fin 64 where
  toFun i := (![1,16,17,18,19,24,25] : Fin 7→Fin 64) i
  inj' := by decide +kernel
def dimensionsEmbedding : Fin 8 ↪ Fin 64 where
  toFun i := (![5,6,2,3,24,25,13,26] : Fin 8→Fin 64) i
  inj' := by decide +kernel
def firstReadEmbedding : Fin 8 ↪ Fin 64 where
  toFun i := (![7,2,20,24,25,26,27,28] : Fin 8→Fin 64) i
  inj' := by decide +kernel
def secondReadEmbedding : Fin 8 ↪ Fin 64 where
  toFun i := (![8,3,21,24,25,26,27,28] : Fin 8→Fin 64) i
  inj' := by decide +kernel
def numeratorEmbedding : Fin 16 ↪ Fin 64 where
  toFun i := (![24,25,26,27,28,29,30,32,33,20,21,14,19,31,55,56] : Fin 16→Fin 64) i
  inj' := by decide +kernel
def denominatorEmbedding : Fin 16 ↪ Fin 64 where
  toFun i := (![24,25,26,27,28,29,30,32,33,22,10,15,18,55,56,57] : Fin 16→Fin 64) i
  inj' := by decide +kernel
def accumulatorEmbedding : Fin 16 ↪ Fin 64 where
  toFun i := (![24,25,26,27,28,29,30,32,33,11,12,20,22,34,35,36] : Fin 16→Fin 64) i
  inj' := by decide +kernel
lemma update_geometricNumerator (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (14:Fin 64) xs=store p {v with geometricNumerator:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_geometricDenominator (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (15:Fin 64) xs=store p {v with geometricDenominator:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_exponent (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (16:Fin 64) xs=store p {v with exponent:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_negative (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (17:Fin 64) xs=store p {v with negative:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_dyadicDenominator (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (18:Fin 64) xs=store p {v with dyadicDenominator:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_dyadicNumerator (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (19:Fin 64) xs=store p {v with dyadicNumerator:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_firstNumerator (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (20:Fin 64) xs=store p {v with firstNumerator:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_secondNumerator (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (21:Fin 64) xs=store p {v with secondNumerator:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_itemDenominator (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (22:Fin 64) xs=store p {v with itemDenominator:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_answer (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (31:Fin 64) xs=store p {v with answer:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_query (p : Parameters) (v : Values) (xs : BitString) :
    Function.update (store p v) (63:Fin 64) xs=store p {v with query:=xs} := by
  funext i;fin_cases i <;> rfl

lemma update_degree (p : Parameters) (v : Values) (d : ℕ) :
    Function.update (store p v) (13:Fin 64) (List.replicate d true)=store p {v with degree:=d} := by
  funext i;fin_cases i <;> rfl
lemma update_accumulator (p : Parameters) (v : Values) (a : ℤ×ℤ) :
    Function.update (Function.update (store p v) (11:Fin 64) (signedBits a.1)) (12:Fin 64) (signedBits a.2)=
      store p {v with accumulator:=a} := by
  funext i;fin_cases i <;> rfl

lemma update_r (p : Parameters) (v : Values) (n : ℕ) :
    Function.update (store p v) (2:Fin 64) (List.replicate n true)=store {p with r:=n} v := by
  funext i;fin_cases i <;> rfl

lemma update_s (p : Parameters) (v : Values) (n : ℕ) :
    Function.update (store p v) (3:Fin 64) (List.replicate n true)=store {p with s:=n} v := by
  funext i;fin_cases i <;> rfl

lemma update_u (p : Parameters) (v : Values) (n : ℕ) :
    Function.update (store p v) (4:Fin 64) (List.replicate n true)=store {p with u:=n} v := by
  funext i;fin_cases i <;> rfl
end HiddenCircuits.Circuit.Runtime.SourceSample
