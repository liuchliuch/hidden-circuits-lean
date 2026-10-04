import HiddenCircuits.Complexity.PolynomialBounds
import HiddenCircuits.Complexity.OracleRepeat
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreams
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime
import HiddenCircuits.Complexity.RecoveryBitBounds

/-! The common one-dimensional denominator is generated and multiplied by real bit programs. -/
namespace HiddenCircuits.Complexity.GridDenominatorRuntime
open OracleBlock BinaryArithmetic Polynomial
open scoped BigOperators

def denominatorList (d : ℕ) : List ℤ := (List.finRange (d+1)).map (interpolationDenominator d)
def degreeValue (d : ℕ) : ℤ := ∏ i : Fin (d+1), interpolationDenominator d i

 theorem denominatorList_words (d : ℕ) : (denominatorList d).map signedBits=denominatorWords d := by
  simp [denominatorList,denominatorWords,List.map_map,Function.comp_def]
 theorem denominatorList_prod (d : ℕ) : (denominatorList d).prod=degreeValue d := by
  exact (Fin.prod_univ_def (interpolationDenominator d)).symm

noncomputable def streamBound : Polynomial ℕ := (X+1)*(2*((X+1)^2+2)+2)+2
noncomputable def degreeTime : Polynomial ℕ :=
  weightStreamsTime+productAccumulatorTime.comp streamBound+streamBound+20

def degreeStore (input numerator acc : BitString) : Store 17 := fun i =>
  if i.val=0 then input else if i.val=1 then numerator else if i.val=17 then acc else []
def streamsEmbedding : Fin 17 ↪ Fin 18 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 18 => z.val) h)
def productEmbedding : Fin 7 ↪ Fin 18 where
  toFun i := if i.val=0 then 17 else if i.val=6 then 0 else ⟨i.val,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def degreeProduct : OracleBlock 17 :=
  seq (rename weightStreams streamsEmbedding)
    (seq (clear 1) (seq (prepend 17 (signedBits 1)) (rename productAccumulator productEmbedding)))

theorem degree_executes (g : BitString → ℕ) (d : ℕ) :
    ∃ c, degreeProduct.Executes g (degreeStore (List.replicate d true) [] [])
      (degreeStore [] [] (signedBits (degreeValue d))) c ∧ c≤degreeTime.eval d := by
  let ds := encodeBitList (denominatorWords d)
  let ns := encodeBitList (negativeNumeratorWords d)
  let s₀ := degreeStore (List.replicate d true) [] []
  let s₁ := degreeStore ds ns []
  let s₂ := degreeStore ds [] []
  let s₃ := degreeStore ds [] (signedBits 1)
  let s₄ := degreeStore [] [] (signedBits (degreeValue d))
  obtain ⟨a,ha,hab⟩ := weightStreams_executes g d
  have h₁ : (rename weightStreams streamsEmbedding).Executes g s₀ s₁ a := by
    apply rename_executes_to weightStreams streamsEmbedding g ha
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      have h17 : j.val=17 := by
        by_contra h
        exact hj ⟨j.val,by omega⟩ (Fin.ext rfl)
      simp [s₀,s₁,degreeStore,h17]
  have h₂ : (clear (1:Fin 18)).Executes g s₁ s₂ (ns.length+1) := by
    convert clear_executes g (1:Fin 18) s₁ using 1
    funext i;fin_cases i <;> rfl
  have h₃ : (prepend (17:Fin 18) (signedBits 1)).Executes g s₂ s₃ 7 := by
    convert prepend_executes g (17:Fin 18) (signedBits 1) s₂ using 1
    · funext i;fin_cases i <;> simp [s₂,s₃,degreeStore]
  obtain ⟨b,hb,hbb⟩ := productAccumulator_polynomial g (denominatorList d) 1
  rw [denominatorList_words,one_mul,denominatorList_prod] at hb
  have h₄ : (rename productAccumulator productEmbedding).Executes g s₃ s₄ b := by
    apply rename_executes_to productAccumulator productEmbedding g hb
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 6 rfl)
  have hs : operandStreamLength 1 (denominatorList d)≤streamBound.eval d := by
    have hh := denominatorWords_length_bound d
    simp only [operandStreamLength,denominatorList_words]
    have h1 : (signedBits 1).length=2 := by decide +kernel
    rw [h1]
    simpa only [streamBound,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat,weightWordBound,Nat.add_comm] using Nat.add_le_add_left hh 2
  have hp := polynomial_nat_eval_mono productAccumulatorTime hs
  dsimp only at hp
  have hn := negativeNumeratorWords_length_bound d
  refine ⟨a+(ns.length+1+(7+b+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  simp only [degreeTime,eval_add,eval_comp,eval_ofNat]
  have hns : ns.length≤streamBound.eval d := by
    dsimp [ns]
    apply hn.trans
    simp only [streamBound,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat,weightWordBound]
    omega
  omega

 theorem degree_queryFree : degreeProduct.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ weightStreams_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (prepend_queryFree _ _)
      (rename_queryFree _ _ productAccumulator_queryFree)))

 theorem degreeValue_length (d : ℕ) : (signedBits (degreeValue d)).length≤(d^2+1)*(d+1)+2 := by
  apply signedBits_length_of_abs_bound
  simpa [degreeValue] using int_prod_envelope Finset.univ (interpolationDenominator d) (d^2+1)
    (fun i _ => interpolationDenominator_envelope d i)
end HiddenCircuits.Complexity.GridDenominatorRuntime
