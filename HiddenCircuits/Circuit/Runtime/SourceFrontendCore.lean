import HiddenCircuits.Circuit.Runtime.SourceMetadata
import HiddenCircuits.Circuit.Runtime.SourceSampleFrame
import HiddenCircuits.Circuit.Runtime.WordCount

/-! Physical source metadata layout and fixed
embeddings for the two spectral-weight computations and array counts. -/
namespace HiddenCircuits.Circuit.Runtime.SourceFrontend
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

def rawStore {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (wire : BitString) : Store 63 := fun i =>
  if i.val=0 then circuitBits n w else if i.val=1 then List.replicate a true
  else if i.val=5 then List.replicate (forbidOccurrences w) true
  else if i.val=6 then List.replicate (signOccurrences w) true
  else if i.val=23 then wire else []

def metadataEmbedding : Fin 36 ↪ Fin 64 where
  toFun i := (![0,1,23,5,6,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54] : Fin 36→Fin 64) i
  inj' := by decide +kernel
noncomputable def metadata : OracleBlock 63 := SourceMetadata.on metadataEmbedding

theorem metadata_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n) :
    ∃c,metadata.Executes g (Function.update (fun _ : Fin 64=>[]) 0 (GraphInput.encode ⟨n,G⟩))
      (rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) (List.replicate n true)) c ∧
      c≤SourceMetadata.time.eval (GraphInput.encode ⟨n,G⟩).length := by
  obtain ⟨c,hc,hb⟩:=SourceMetadata.on_executes metadataEmbedding g
    (Function.update (fun _ : Fin 64=>[]) 0 (GraphInput.encode ⟨n,G⟩)) G (by funext i;fin_cases i <;> rfl)
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext i;fin_cases i <;> rfl

lemma rawStore_update_wire {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (wire xs : BitString) :
    Function.update (rawStore w a wire) (23:Fin 64) xs=rawStore w a xs := by
  funext i;fin_cases i <;> rfl
lemma rawStore_wire_bound {n : ℕ} (w : List (ConstraintGate n)) (a B : ℕ) (wire xs : BitString)
    (h : ∀i,(rawStore w a wire i).length≤B) (hxs : xs.length≤wire.length) :
    ∀i,(rawStore w a xs i).length≤B := by
  intro i
  by_cases hi:i.val=23
  · have hw:=h 23
    simpa [rawStore,hi] using hxs.trans hw
  · simpa [rawStore,hi] using h i

def firstEmbedding : Fin 36 ↪ Fin 64 where
  toFun i := (![5,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,9,7] : Fin 36→Fin 64) i
  inj' := by decide +kernel
def secondEmbedding : Fin 36 ↪ Fin 64 where
  toFun i := (![6,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,10,8] : Fin 36→Fin 64) i
  inj' := by decide +kernel
def firstCountEmbedding : Fin 6 ↪ Fin 64 where
  toFun i := (![7,24,25,26,27,58] : Fin 6→Fin 64) i
  inj' := by decide +kernel
def secondCountEmbedding : Fin 6 ↪ Fin 64 where
  toFun i := (![8,24,25,26,27,59] : Fin 6→Fin 64) i
  inj' := by decide +kernel

def firstStore {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) : Store 63 :=
  Function.update (Function.update (rawStore w a []) 9 (signedBits (SpectralWeights.denominator (forbidOccurrences w))))
    7 (SpectralWeightsProgram.numeratorStream (forbidOccurrences w) false)
def spectralStore {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) : Store 63 :=
  Function.update (Function.update (firstStore w a) 10 (signedBits (SpectralWeights.denominator (signOccurrences w))))
    8 (SpectralWeightsProgram.numeratorStream (signOccurrences w) true)
def countedStore {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) : Store 63 :=
  Function.update (Function.update (spectralStore w a) 58 (List.replicate (Fintype.card (SpectralIndex (forbidOccurrences w))) true))
    59 (List.replicate (Fintype.card (SpectralIndex (signOccurrences w))) true)
def initializedStore {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) : Store 63 :=
  Function.update (Function.update (SourceSample.store (SourceSample.canonical w a 0 0 0) {accumulator:=(0,1)})
    58 (List.replicate (Fintype.card (SpectralIndex (forbidOccurrences w))) true))
    59 (List.replicate (Fintype.card (SpectralIndex (signOccurrences w))) true)

noncomputable def spectral : OracleBlock 63 := seq (clear 23)
  (seq (SourceSpectralSetup.on firstEmbedding false) (SourceSpectralSetup.on secondEmbedding true))
noncomputable def spectralTime : Polynomial ℕ := X+2*SourceSpectralSetup.time+5

theorem spectral_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (wire : BitString) (B : ℕ)
    (hB : ∀i,(rawStore w a wire i).length≤B) :
    ∃c,spectral.Executes g (rawStore w a wire) (spectralStore w a) c ∧ c≤spectralTime.eval B := by
  have hc : (clear (23:Fin 64)).Executes g (rawStore w a wire) (rawStore w a []) (wire.length+1) := by
    simpa only [rawStore_update_wire] using clear_executes g (23:Fin 64) (rawStore w a wire)
  obtain ⟨b,hb,hbb⟩:=SourceSpectralSetup.on_executes firstEmbedding g (rawStore w a []) (forbidOccurrences w) false
    (by funext i;fin_cases i <;> rfl)
  obtain ⟨c,hc',hcb⟩:=SourceSpectralSetup.on_executes secondEmbedding g (firstStore w a) (signOccurrences w) true
    (by funext i;fin_cases i <;> rfl)
  have hw : wire.length≤B := hB 23
  have hf : forbidOccurrences w≤B := by simpa [rawStore] using hB 5
  have hz : signOccurrences w≤B := by simpa [rawStore] using hB 6
  have hbf:=hbb.trans (polynomial_nat_eval_mono SourceSpectralSetup.time hf)
  have hbz:=hcb.trans (polynomial_nat_eval_mono SourceSpectralSetup.time hz)
  dsimp only at hbf hbz
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hb hc'),?_⟩
  simp only [spectralTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SourceFrontend
