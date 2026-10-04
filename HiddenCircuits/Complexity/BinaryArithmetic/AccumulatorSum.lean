import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct
import HiddenCircuits.Complexity.BinaryArithmetic.SignedAddition

/-! Actual canonical signed summation over an encoded list. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

def SumBitBound (B : ℕ) : ℤ → List ℤ → Prop
  | a, [] => (signedBits a).length≤B
  | a, z::zs => (signedBits a).length≤B ∧ (signedBits z).length≤B ∧ SumBitBound B (a+z) zs

lemma SumBitBound.head {B : ℕ} {a : ℤ} {zs : List ℤ} (h : SumBitBound B a zs) :
    (signedBits a).length≤B := by
  cases zs with
  | nil => exact h
  | cons z zs => exact h.1

def sumStore (acc item tmp flag stream : BitString) : Store 7 := fun i =>
  if i.val=0 then acc else if i.val=1 then item else if i.val=3 then tmp
  else if i.val=4 then flag else if i.val=7 then stream else []

def sumParseEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 7 else if i.val=1 then 1 else if i.val=2 then 3 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def sumParse : OracleBlock 7 := GraphVerifier.Runtime.unpairOn sumParseEmbedding

theorem sumParse_executes (g : BitString → ℕ) (acc item rest : BitString) :
    sumParse.Executes g (sumStore acc [] [] [] (pairBits item rest))
      (sumStore acc item [] [true] rest) (5*item.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes sumParseEmbedding g
    (sumStore acc [] [] [] (pairBits item rest)) (sumStore acc item [] [true] rest) (pairBits item rest)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by
      intro j hj
      fin_cases j
      · rfl
      · exact False.elim (hj 1 rfl)
      · rfl
      · rfl
      · exact False.elim (hj 3 rfl)
      · rfl
      · rfl
      · exact False.elim (hj 0 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost]; omega

def sumAddEmbedding : Fin 7 ↪ Fin 8 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)

noncomputable def sumAdd : OracleBlock 7 := rename signedAddClean sumAddEmbedding

theorem sumAdd_executes (g : BitString → ℕ) (a z : ℤ) (rest : BitString) :
    ∃ t, sumAdd.Executes g (sumStore (signedBits a) (signedBits z) [] [] rest)
      (sumStore (signedBits (a+z)) [] [] [] rest) t ∧
      t≤400*(max (Computability.encodeNat a.natAbs).length (Computability.encodeNat z.natAbs).length+1) := by
  obtain ⟨t,ht,hb⟩ := signedAddClean_executes g a z
  refine ⟨t,?_,hb⟩
  apply rename_executes_to signedAddClean sumAddEmbedding g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj
    fin_cases j
    · exact False.elim (hj 0 rfl)
    · exact False.elim (hj 1 rfl)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

noncomputable def sumBody : OracleBlock 7 := seq sumParse (seq (clear 4) sumAdd)

def sumIterationBound (B : ℕ) : ℕ := 500*(B+1)

theorem sumBody_executes (g : BitString → ℕ) (a z : ℤ) (rest : BitString) (B : ℕ)
    (ha : (signedBits a).length≤B) (hz : (signedBits z).length≤B) :
    ∃ t, sumBody.Executes g (sumStore (signedBits a) [] [] [] (pairBits (signedBits z) rest))
      (sumStore (signedBits (a+z)) [] [] [] rest) t ∧ t+2≤sumIterationBound B := by
  have hparse := sumParse_executes g (signedBits a) (signedBits z) rest
  have hclear : (clear (4 : Fin 8)).Executes g (sumStore (signedBits a) (signedBits z) [] [true] rest)
      (sumStore (signedBits a) (signedBits z) [] [] rest) 2 := by
    convert clear_executes g (4 : Fin 8) (sumStore (signedBits a) (signedBits z) [] [true] rest) using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨t,ht,hbound⟩ := sumAdd_executes g a z rest
  have h := seq_executes _ _ g hparse (seq_executes _ _ g hclear ht)
  refine ⟨_,h,?_⟩
  simp only [signedBits,List.length_cons] at ha hz
  unfold sumIterationBound
  simp only [signedBits,List.length_cons]
  omega

noncomputable def sumAccumulator : OracleBlock 7 := whilePop 7 skip sumBody

theorem sumAccumulator_while (g : BitString → ℕ) (zs : List ℤ) (a : ℤ) (B : ℕ)
    (hB : SumBitBound B a zs) :
    ∃ t, WhileExecution (7 : Fin 8) skip sumBody g
      (sumStore (signedBits a) [] [] [] (encodeBitList (zs.map signedBits)))
      (sumStore (signedBits (zs.foldl (·+·) a)) [] [] [] []) t ∧
      t≤1+zs.length*sumIterationBound B := by
  induction zs generalizing a with
  | nil => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | cons z zs ih =>
    obtain ⟨ha,hz,htail⟩ := hB
    obtain ⟨body,hbody,hbodyBound⟩ := sumBody_executes g a z (encodeBitList (zs.map signedBits)) B ha hz
    obtain ⟨tail,ht,hbound⟩ := ih (a+z) htail
    refine ⟨2+body+tail,?_,?_⟩
    · have hs : Function.update
          (sumStore (signedBits a) [] [] [] (encodeBitList ((z::zs).map signedBits))) (7 : Fin 8)
          (pairBits (signedBits z) (encodeBitList (zs.map signedBits))) =
          sumStore (signedBits a) [] [] [] (pairBits (signedBits z) (encodeBitList (zs.map signedBits))) := by
        funext i; fin_cases i <;> rfl
      have hw := WhileExecution.one
        (s := sumStore (signedBits a) [] [] [] (encodeBitList ((z::zs).map signedBits)))
        (rest := pairBits (signedBits z) (encodeBitList (zs.map signedBits)))
        (by rfl) (by rw [hs]; exact hbody) ht
      convert hw using 1 <;> omega
    · simp only [List.length_cons]
      nlinarith

/-- A real finite-program sum fold with linear cost in list length and B. -/
theorem sumAccumulator_executes (g : BitString → ℕ) (zs : List ℤ) (a : ℤ) (B : ℕ)
    (hB : SumBitBound B a zs) :
    ∃ t, sumAccumulator.Executes g
      (sumStore (signedBits a) [] [] [] (encodeBitList (zs.map signedBits)))
      (sumStore (signedBits (zs.foldl (·+·) a)) [] [] [] []) t ∧
      t≤1+zs.length*sumIterationBound B := by
  obtain ⟨t,ht,hbound⟩ := sumAccumulator_while g zs a B hB
  exact ⟨t,whilePop_executes _ _ _ _ ht,hbound⟩

lemma sumAccumulator_queryFree : sumAccumulator.QueryFree := by
  have hp : sumParse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have ha : sumAdd.QueryFree := rename_queryFree _ _ signedAddClean_queryFree
  exact whilePop_queryFree _ _ _ skip_queryFree
    (seq_queryFree _ _ hp (seq_queryFree _ _ (clear_queryFree _) ha))

end HiddenCircuits.Complexity.BinaryArithmetic
