import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct

/-! Actual indexed extraction from a self-delimiting word list. This supports
both sampled-partner decoding and selecting a boosted empirical count. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def lookupStore (source index value tmp flag : BitString) : Store 4 := fun i =>
  if i.val=0 then source else if i.val=1 then index else if i.val=2 then value
  else if i.val=3 then tmp else flag

def listParseEmbedding : Fin 4 ↪ Fin 5 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 2 else if i.val=2 then 3 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def listParse : OracleBlock 4 := GraphVerifier.Runtime.unpairOn listParseEmbedding
noncomputable def discardParsed : OracleBlock 4 := seq listParse (seq (clear 2) (clear 4))
noncomputable def discardWord : OracleBlock 4 := branchPop 0 skip skip discardParsed
noncomputable def discardWords : OracleBlock 4 := whilePop 1 discardWord discardWord
noncomputable def retainParsed : OracleBlock 4 := seq listParse (seq (clear 4) (clear 0))
noncomputable def retainWord : OracleBlock 4 := branchPop 0 skip skip retainParsed
noncomputable def listLookup : OracleBlock 4 := seq discardWords retainWord

 theorem listParse_executes (g : BitString → ℕ) (word rest index : BitString) :
    listParse.Executes g (lookupStore (pairBits word rest) index [] [] [])
      (lookupStore rest index word [] [true]) (5*word.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes listParseEmbedding g
    (lookupStore (pairBits word rest) index [] [] []) (lookupStore rest index word [] [true])
    (pairBits word rest)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by
      intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair, BinaryArithmetic.pair_parse_cost]
  omega

 theorem discardWord_executes (g : BitString → ℕ) (word rest index : BitString) :
    discardWord.Executes g (lookupStore (true::pairBits word rest) index [] [] [])
      (lookupStore rest index [] [] []) (6*word.length+12) := by
  have hc : (clear (2 : Fin 5)).Executes g (lookupStore rest index word [] [true])
      (lookupStore rest index [] [] [true]) (word.length+1) := by
    convert clear_executes g (2 : Fin 5) (lookupStore rest index word [] [true]) using 1
    funext i; fin_cases i <;> rfl
  have hf : (clear (4 : Fin 5)).Executes g (lookupStore rest index [] [] [true])
      (lookupStore rest index [] [] []) 2 := by
    convert clear_executes g (4 : Fin 5) (lookupStore rest index [] [] [true]) using 1
    funext i; fin_cases i <;> rfl
  have hp := seq_executes _ _ g (listParse_executes g word rest index) (seq_executes _ _ g hc hf)
  have h := branchPop_true (0 : Fin 5) skip skip discardParsed g
    (s := lookupStore (true::pairBits word rest) index [] [] []) (rest := pairBits word rest) rfl
    (by convert hp using 1; funext i; fin_cases i <;> rfl)
  convert h using 1 <;> omega

 theorem discardWords_execution (g : BitString → ℕ) (pre rest : List BitString) :
    ∃ t, WhileExecution (1 : Fin 5) discardWord discardWord g
      (lookupStore (encodeBitList (pre++rest)) (List.replicate pre.length true) [] [] [])
      (lookupStore (encodeBitList rest) [] [] [] []) t ∧ t ≤ 7*(encodeBitList pre).length+1 := by
  induction pre with
  | nil => exact ⟨1,by simpa using WhileExecution.empty (lookupStore (encodeBitList rest) [] [] [] []) rfl,by simp [encodeBitList]⟩
  | cons word pre ih =>
    obtain ⟨tt,ht,hbt⟩ := ih
    have hb := discardWord_executes g word (encodeBitList (pre++rest)) (List.replicate pre.length true)
    have hpop : Function.update
        (lookupStore (encodeBitList ((word::pre)++rest)) (List.replicate (word::pre).length true) [] [] [])
        (1 : Fin 5) (List.replicate pre.length true) =
        lookupStore (true::pairBits word (encodeBitList (pre++rest))) (List.replicate pre.length true) [] [] [] := by
      funext i; fin_cases i <;> rfl
    have h := WhileExecution.one
      (s := lookupStore (encodeBitList ((word::pre)++rest)) (List.replicate (word::pre).length true) [] [] [])
      (rest := List.replicate pre.length true) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨2+(6*word.length+12)+tt,?_,?_⟩
    · convert h using 1 <;> omega
    · simp only [encodeBitList, List.length_cons, pairBits_length]
      omega

 theorem retainWord_executes (g : BitString → ℕ) (word rest : BitString) :
    retainWord.Executes g (lookupStore (true::pairBits word rest) [] [] [] [])
      (lookupStore [] [] word [] []) (5*word.length+rest.length+12) := by
  have hf : (clear (4 : Fin 5)).Executes g (lookupStore rest [] word [] [true])
      (lookupStore rest [] word [] []) 2 := by
    convert clear_executes g (4 : Fin 5) (lookupStore rest [] word [] [true]) using 1
    funext i; fin_cases i <;> rfl
  have hr : (clear (0 : Fin 5)).Executes g (lookupStore rest [] word [] [])
      (lookupStore [] [] word [] []) (rest.length+1) := by
    convert clear_executes g (0 : Fin 5) (lookupStore rest [] word [] []) using 1
    funext i; fin_cases i <;> rfl
  have hp := seq_executes _ _ g (listParse_executes g word rest []) (seq_executes _ _ g hf hr)
  have h := branchPop_true (0 : Fin 5) skip skip retainParsed g
    (s := lookupStore (true::pairBits word rest) [] [] [] []) (rest := pairBits word rest) rfl
    (by convert hp using 1; funext i; fin_cases i <;> rfl)
  convert h using 1 <;> omega

/-- Indexed word extraction includes discarding every unused suffix and all
parser work. Its time is linear in the actual serialized input length. -/
theorem listLookup_executes (g : BitString → ℕ) (pre suffix : List BitString) (word : BitString) :
    ∃ t, listLookup.Executes g
      (lookupStore (encodeBitList (pre++word::suffix)) (List.replicate pre.length true) [] [] [])
      (lookupStore [] [] word [] []) t ∧
      t ≤ 7*(encodeBitList pre).length+5*word.length+(encodeBitList suffix).length+15 := by
  obtain ⟨td,hd,hbd⟩ := discardWords_execution g pre (word::suffix)
  have h := seq_executes _ _ g (whilePop_executes _ _ _ _ hd) (retainWord_executes g word (encodeBitList suffix))
  refine ⟨_,h,?_⟩
  omega

 theorem encodeBitList_append_length (xs ys : List BitString) :
    (encodeBitList (xs++ys)).length = (encodeBitList xs).length+(encodeBitList ys).length := by
  simp [encodeBitList_length, List.map_append, List.sum_append]
  omega

 theorem listLookup_linear (g : BitString → ℕ) (pre suffix : List BitString) (word : BitString) :
    ∃ t, listLookup.Executes g
      (lookupStore (encodeBitList (pre++word::suffix)) (List.replicate pre.length true) [] [] [])
      (lookupStore [] [] word [] []) t ∧ t ≤ 7*(encodeBitList (pre++word::suffix)).length+15 := by
  obtain ⟨t,ht,hb⟩ := listLookup_executes g pre suffix word
  refine ⟨t,ht,?_⟩
  rw [encodeBitList_append_length]
  simp only [encodeBitList, List.length_cons, pairBits_length]
  omega

 theorem listLookup_index (g : BitString → ℕ) (xs : List BitString) (i : Fin xs.length) :
    ∃ t, listLookup.Executes g (lookupStore (encodeBitList xs) (List.replicate i.val true) [] [] [])
      (lookupStore [] [] (xs.get i) [] []) t ∧ t ≤ 7*(encodeBitList xs).length+15 := by
  have h := listLookup_linear g (xs.take i.val) (xs.drop (i.val+1)) (xs.get i)
  have he : xs.take i.val ++ xs.get i :: xs.drop (i.val+1)=xs := by
    rw [List.get_eq_getElem, List.getElem_cons_drop, List.take_append_drop]
  rw [he] at h
  simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)] using h

end HiddenCircuits.Approximation.SelfReduction.Runtime
