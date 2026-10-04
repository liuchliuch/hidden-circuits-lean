import HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutputUnary

/-! The signed denominator is produced by the real product accumulator. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial

noncomputable def foldProduct : OracleBlock 6 :=
  seq (moveOn 0 6 1 (by decide) (by decide) (by decide))
    (seq (prepend 0 (signedBits 1)) productAccumulator)
noncomputable def foldTime : Polynomial ℕ := 6*X+productAccumulatorTime.comp (X+2)+16

 theorem foldProduct_executes (g : BitString → ℕ) (xs : List ℕ) :
    ∃ t, foldProduct.Executes g (clean (encodeBitList (signedWords xs)))
      (clean (signedBits (xs.prod : ℤ))) t ∧
      t≤foldTime.eval (encodeBitList (signedWords xs)).length := by
  let word := encodeBitList (signedWords xs)
  let s1 := productStore [] [] [] [] [] [] word
  let s2 := productStore (signedBits 1) [] [] [] [] [] word
  have hm : (moveOn (0:Fin 7) 6 1 (by decide) (by decide) (by decide)).Executes g
      (clean word) s1 (6*word.length+5) := by
    convert moveOn_executes g (0:Fin 7) 6 1 (by decide) (by decide) (by decide) (clean word) rfl using 1
    funext i; fin_cases i <;> simp [clean,s1,productStore]
  have hp : (prepend (0:Fin 7) (signedBits 1)).Executes g s1 s2 7 := by
    convert prepend_executes g (0:Fin 7) (signedBits 1) s1 using 1
    · funext i; fin_cases i <;> rfl
  obtain ⟨t,ht,hb⟩ := productAccumulator_polynomial g (xs.map (fun n : ℕ => (n : ℤ))) 1
  have ht' : productAccumulator.Executes g s2 (clean (signedBits (xs.prod : ℤ))) t := by
    convert ht using 1
    · funext i; fin_cases i <;> simp [s2,word,signedWords,List.map_map,Function.comp_def,productStore]
    · funext i; fin_cases i <;> simp [clean,productStore,Nat.cast_list_prod]
  refine ⟨_,seq_executes _ _ g hm (seq_executes _ _ g hp ht'),?_⟩
  have he : operandStreamLength 1 (xs.map (fun n : ℕ => (n : ℤ)))=word.length+2 := by
    have hOne : (signedBits (1:ℤ)).length=2 := by decide
    simp only [operandStreamLength,word,signedWords,List.map_map,Function.comp_def,hOne]
    omega
  rw [he] at hb
  simp only [foldTime,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  change 6*word.length+5+(7+t+2)+2≤6*word.length+productAccumulatorTime.eval (word.length+2)+16
  omega

 theorem foldProduct_queryFree : foldProduct.QueryFree := seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (prepend_queryFree _ _) productAccumulator_queryFree)

noncomputable def denominator : OracleBlock 6 := seq mapSigned foldProduct
noncomputable def denominatorTime : Polynomial ℕ := mapTime+foldTime.comp (X+mapTime)+2

 theorem clean_bound {k : ℕ} (word : BitString) : ∀ i, (clean (k:=k) word i).length≤word.length := by
  intro i
  by_cases hi : i=0
  · subst i; simp [clean]
  · simp [clean,hi]

 theorem clean_output_bound {k : ℕ} {B : OracleBlock k} {g : BitString → ℕ}
    {x y : BitString} {t : ℕ} (h : B.Executes g (clean x) (clean y) t) : y.length≤x.length+t := by
  simpa using h.stack_bound (clean_bound x) (0:Fin (k+1))

 theorem denominator_executes (g : BitString → ℕ) (xs : List ℕ) :
    ∃ t, denominator.Executes g (clean (encodeBitList (unaryWords xs)))
      (clean (signedBits (xs.prod : ℤ))) t ∧
      t≤denominatorTime.eval (encodeBitList (unaryWords xs)).length := by
  obtain ⟨a,ha,hab⟩ := mapSigned_executes g xs
  obtain ⟨b,hb,hbb⟩ := foldProduct_executes g xs
  have hl := clean_output_bound ha
  have hmono := polynomial_nat_eval_mono foldTime (hl.trans (Nat.add_le_add_left hab _))
  dsimp only at hmono
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [denominatorTime,eval_add,eval_comp,eval_X,eval_ofNat]
  omega

 theorem denominator_queryFree : denominator.QueryFree := seq_queryFree _ _ mapSigned_queryFree foldProduct_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime.EstimateOutput
