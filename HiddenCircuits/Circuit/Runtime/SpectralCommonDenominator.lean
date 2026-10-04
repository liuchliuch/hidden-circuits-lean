import HiddenCircuits.Circuit.Runtime.SpectralTable
import HiddenCircuits.Circuit.SpectralWeightData

/-! The common denominator is computed by a real signed-product stream fold. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCommonDenominator
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

def store (out stream : BitString) : Store 6 := productStore out [] [] [] [] [] stream
noncomputable def program : OracleBlock 6 := seq (moveOn 0 6 2 (by decide) (by decide) (by decide))
  (seq (prepend 0 (signedBits 1)) productAccumulator)
noncomputable def time : Polynomial ℕ := productAccumulatorTime.comp (X+2)+6*X+16

theorem program_executes (oracle : BitString → ℕ) (ds : List ℤ) :
    ∃ t, program.Executes oracle (store (encodeBitList (ds.map signedBits)) [])
      (store (signedBits ds.prod) []) t ∧ t≤time.eval (encodeBitList (ds.map signedBits)).length := by
  let input := encodeBitList (ds.map signedBits)
  have h₁ : (moveOn (0:Fin 7) 6 2 (by decide) (by decide) (by decide)).Executes oracle
      (store input []) (store [] input) (6*input.length+5) := by
    convert moveOn_executes oracle (0:Fin 7) 6 2 (by decide) (by decide) (by decide) (store input []) rfl using 1
    funext i;fin_cases i <;> simp [store,productStore]
  have h₂ : (prepend (0:Fin 7) (signedBits 1)).Executes oracle (store [] input) (store (signedBits 1) input) 7 := by
    convert prepend_executes oracle (0:Fin 7) (signedBits 1) (store [] input) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨t,ht,hb⟩ := productAccumulator_polynomial oracle ds 1
  simp only [one_mul] at ht
  refine ⟨(6*input.length+5)+(7+t+2)+2,seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ ht),?_⟩
  have he : operandStreamLength 1 ds=input.length+2 := by change 2+input.length=input.length+2;omega
  rw [he] at hb
  simp only [time,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  change _≤productAccumulatorTime.eval (input.length+2)+6*input.length+16
  omega

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (prepend_queryFree _ _) productAccumulator_queryFree)

noncomputable def programOn {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) (oracle : BitString → ℕ) (s : Store k)
    (ds : List ℤ) (hs : s∘φ=store (encodeBitList (ds.map signedBits)) []) :
    ∃ t, (programOn φ).Executes oracle s (Function.update s (φ 0) (signedBits ds.prod)) t ∧
      t≤time.eval (encodeBitList (ds.map signedBits)).length := by
  obtain ⟨t,ht,hb⟩ := program_executes oracle ds
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ oracle ht hs
  · have he : (Function.update s (φ 0) (signedBits ds.prod))∘φ=Function.update (s∘φ) 0 (signedBits ds.prod) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj;exact Function.update_of_ne (hj 0).symm _ _

theorem programOn_queryFree {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

 def value (g : ℕ) : ℤ := ((spectralIndices g).map (spectralBasisDenominator g)).prod
noncomputable def spectralTime : Polynomial ℕ := time.comp SpectralTable.vectorBound

theorem value_ne_zero (g : ℕ) : value g≠0 :=
  IntegerRatioAccumulator.commonDenominator_ne_zero _ _ (spectralBasisDenominator_ne_zero g)

theorem value_eq_weight_denominator (g : ℕ) (z : ℤ) (k : ℕ) : value g=(spectralWeightData g z k).2 := rfl

theorem value_bits (g : ℕ) : (signedBits (value g)).length≤spectralBasisBitBound g*(g+1)^2+2 := by
  have hh := (spectralWeightData_bits g 0 (by simp) 0).1
  simpa only [signedBits,List.length_cons,encodeNat_length,value_eq_weight_denominator g 0 0] using Nat.add_le_add_right hh 1

theorem program_spectral_executes (oracle : BitString → ℕ) (g : ℕ) :
    ∃ t, program.Executes oracle (store (encodeBitList (SpectralTable.denominators g)) [])
      (store (signedBits (value g)) []) t ∧ t≤spectralTime.eval g := by
  obtain ⟨t,ht,hb⟩ := program_executes oracle ((spectralIndices g).map (spectralBasisDenominator g))
  have he : (((spectralIndices g).map (spectralBasisDenominator g)).map signedBits)=SpectralTable.denominators g := by
    simp [SpectralTable.denominators,List.map_map,Function.comp_def]
  rw [he] at ht hb
  refine ⟨t,ht,hb.trans ?_⟩
  simpa only [spectralTime,eval_comp] using polynomial_nat_eval_mono time (SpectralTable.denominators_length g)
end HiddenCircuits.Circuit.Runtime.SpectralCommonDenominator
