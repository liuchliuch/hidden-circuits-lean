import HiddenCircuits.Circuit.Runtime.SourceFrontendCore

/-! Count the actual emitted numerator arrays and
physically initialize every signed accumulator register from literal bits. -/
namespace HiddenCircuits.Circuit.Runtime.SourceFrontend
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

noncomputable def counts : OracleBlock 63 := seq (WordCount.on firstCountEmbedding) (WordCount.on secondCountEmbedding)
noncomputable def constants : OracleBlock 63 := seq (push 11 false) (seq (prepend 12 (signedBits 1))
  (seq (push 55 false) (seq (push 56 false) (push 57 false))))
noncomputable def program : OracleBlock 63 := seq spectral (seq counts constants)
noncomputable def countTime : Polynomial ℕ := 2*WordCount.time+2
noncomputable def time : Polynomial ℕ := spectralTime+countTime.comp (X+spectralTime)+40

def numeratorWords (d : ℕ) (mode : Bool) : List BitString :=
  ((List.ofFn (fun j : Fin (Fintype.card (SpectralIndex d)) =>
    (spectralWeightData d (SpectralTargets.base mode) j.val).1)).map signedBits)
lemma numeratorWords_length (d : ℕ) (mode : Bool) :
    (numeratorWords d mode).length=Fintype.card (SpectralIndex d) := by simp [numeratorWords]
lemma numeratorWords_encode (d : ℕ) (mode : Bool) :
    encodeBitList (numeratorWords d mode)=SpectralWeightsProgram.numeratorStream d mode :=
  (SpectralWeightsProgram.numeratorStream_eq d mode).symm

set_option maxHeartbeats 700000 in
theorem counts_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (a B : ℕ)
    (hB : ∀i,(spectralStore w a i).length≤B) :
    ∃c,counts.Executes g (spectralStore w a) (countedStore w a) c ∧ c≤countTime.eval B := by
  have hfirst : spectralStore w a∘firstCountEmbedding=
      WordCount.store (encodeBitList (numeratorWords (forbidOccurrences w) false)) [] [] 0 := by
    rw [numeratorWords_encode]
    funext i;fin_cases i <;> rfl
  obtain ⟨b,hb,hbb⟩:=WordCount.on_executes firstCountEmbedding g (spectralStore w a)
    (numeratorWords (forbidOccurrences w) false) hfirst
  simp only [numeratorWords_length,numeratorWords_encode] at hb hbb
  have hsecond : (Function.update (spectralStore w a) (firstCountEmbedding 5)
      (List.replicate (Fintype.card (SpectralIndex (forbidOccurrences w))) true))∘secondCountEmbedding=
      WordCount.store (encodeBitList (numeratorWords (signOccurrences w) true)) [] [] 0 := by
    rw [numeratorWords_encode]
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hc,hcb⟩:=WordCount.on_executes secondCountEmbedding g _
    (numeratorWords (signOccurrences w) true) hsecond
  simp only [numeratorWords_length,numeratorWords_encode] at hc hcb
  have hf : (SpectralWeightsProgram.numeratorStream (forbidOccurrences w) false).length≤B := hB 7
  have hz : (SpectralWeightsProgram.numeratorStream (signOccurrences w) true).length≤B := hB 8
  have hbf:=hbb.trans (polynomial_nat_eval_mono WordCount.time hf)
  have hbz:=hcb.trans (polynomial_nat_eval_mono WordCount.time hz)
  dsimp only at hbf hbz
  refine ⟨_,seq_executes _ _ g hb hc,?_⟩
  simp only [countTime,eval_add,eval_mul,eval_ofNat]
  omega

set_option maxHeartbeats 700000 in
theorem constants_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) :
    constants.Executes g (countedStore w a) (initializedStore w a) 19 := by
  let s0:=countedStore w a
  let s1:=Function.update s0 (11:Fin 64) [false]
  let s2:=Function.update s1 (12:Fin 64) (signedBits 1)
  let s3:=Function.update s2 (55:Fin 64) [false]
  let s4:=Function.update s3 (56:Fin 64) [false]
  have h1 : (push (11:Fin 64) false).Executes g s0 s1 1 := by
    simpa only [s0,s1,show countedStore w a 11=[] from rfl] using push_executes g (11:Fin 64) false s0
  have h2 : (prepend (12:Fin 64) (signedBits 1)).Executes g s1 s2 7 := by
    simpa only [s2,show s1 12=[] from rfl,List.append_nil] using prepend_executes g (12:Fin 64) (signedBits 1) s1
  have h3 : (push (55:Fin 64) false).Executes g s2 s3 1 := by
    simpa only [s3,show s2 55=[] from rfl] using push_executes g (55:Fin 64) false s2
  have h4 : (push (56:Fin 64) false).Executes g s3 s4 1 := by
    simpa only [s4,show s3 56=[] from rfl] using push_executes g (56:Fin 64) false s3
  have h5 : (push (57:Fin 64) false).Executes g s4 (initializedStore w a) 1 := by
    convert push_executes g (57:Fin 64) false s4 using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5)))

theorem program_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (wire : BitString) (B : ℕ)
    (hB : ∀i,(rawStore w a wire i).length≤B) :
    ∃c,program.Executes g (rawStore w a wire) (initializedStore w a) c ∧ c≤time.eval B := by
  obtain ⟨c1,h1,hb1⟩:=spectral_executes g w a wire B hB
  obtain ⟨c2,h2,hb2⟩:=counts_executes g w a (B+c1) (h1.stack_bound hB)
  have h3:=constants_executes g w a
  have hm:=polynomial_nat_eval_mono countTime (show B+c1≤B+spectralTime.eval B by omega)
  dsimp only at hm
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SourceFrontend
