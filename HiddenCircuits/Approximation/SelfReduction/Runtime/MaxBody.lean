import HiddenCircuits.Approximation.SelfReduction.Runtime.MaxSemantics
import HiddenCircuits.Approximation.SelfReduction.Runtime.ReadUnaryLe
import HiddenCircuits.Approximation.SelfReduction.Runtime.ListLookup
import HiddenCircuits.Complexity.OracleMove

/-! A literal right-biased
maximum-scan step parses one unary value, compares it, and copies its index. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
set_option maxHeartbeats 800000

def maxStore (best idx pos item : ℕ) (stream flag : BitString) : Store 10 := fun i =>
  if i.val=0 then List.replicate best true else if i.val=1 then List.replicate idx true
  else if i.val=2 then List.replicate pos true else if i.val=3 then stream
  else if i.val=4 then List.replicate item true else if i.val=5 then flag else []

def maxParseEmbedding : Fin 4 ↪ Fin 11 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 4 else if i.val=2 then 6 else 5
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def maxCompareEmbedding : Fin 6 ↪ Fin 11 where
  toFun i := if i.val=0 then 0 else ⟨i.val+3,by omega⟩
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def maxParse : OracleBlock 10 := GraphVerifier.Runtime.unpairOn maxParseEmbedding
noncomputable def maxCompare : OracleBlock 10 := readUnaryLeOn maxCompareEmbedding
noncomputable def maxReplace : OracleBlock 10 :=
  seq (clear 0) (seq (moveOn 4 0 10 (by decide) (by decide) (by decide))
    (seq (clear 1) (copyOn 2 1 10 (by decide) (by decide) (by decide))))
noncomputable def maxDecision : OracleBlock 10 := branchPop 5 (clear 4) (clear 4) maxReplace
noncomputable def maxBody : OracleBlock 10 := seq maxParse (seq (clear 5)
  (seq maxCompare (seq maxDecision (push 2 true))))

 theorem maxParse_executes (g : BitString → ℕ) (best idx pos item : ℕ) (rest : BitString) :
    maxParse.Executes g (maxStore best idx pos 0 (pairBits (List.replicate item true) rest) [])
      (maxStore best idx pos item rest [true]) (5*item+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes maxParseEmbedding g
    (maxStore best idx pos 0 (pairBits (List.replicate item true) rest) [])
    (maxStore best idx pos item rest [true]) (pairBits (List.replicate item true) rest)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro i hi; fin_cases i; all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,BinaryArithmetic.pair_parse_cost]
  omega

 theorem maxCompare_executes (g : BitString → ℕ) (best idx pos item : ℕ) (rest : BitString) :
    ∃ t, maxCompare.Executes g (maxStore best idx pos item rest [])
      (maxStore best idx pos item rest [decide (best ≤ item)]) t ∧ t ≤ 8*(best+item)+17 := by
  obtain ⟨t,ht,hb⟩ := readUnaryLeOn_executes maxCompareEmbedding g
    (maxStore best idx pos item rest []) (List.replicate best true) (List.replicate item true) []
    (by funext i; fin_cases i <;> rfl)
  refine ⟨t,?_,by simpa using hb⟩
  convert ht using 1
  funext i; fin_cases i <;> simp [maxStore,maxCompareEmbedding]

 theorem maxReplace_executes (g : BitString → ℕ) (best idx pos item : ℕ) (rest : BitString) :
    maxReplace.Executes g (maxStore best idx pos item rest [])
      (maxStore item pos pos 0 rest []) (best+6*item+idx+5*pos+15) := by
  have h1 : (clear (0 : Fin 11)).Executes g (maxStore best idx pos item rest [])
      (maxStore 0 idx pos item rest []) (best+1) := by
    convert clear_executes g (0 : Fin 11) (maxStore best idx pos item rest []) using 1
    · funext i; fin_cases i <;> rfl
    · simp [maxStore]
  have h2 : (moveOn (4 : Fin 11) 0 10 (by decide) (by decide) (by decide)).Executes g
      (maxStore 0 idx pos item rest []) (maxStore item idx pos 0 rest []) (6*item+5) := by
    convert moveOn_executes g (4 : Fin 11) 0 10 (by decide) (by decide) (by decide)
      (maxStore 0 idx pos item rest []) rfl using 1
    · funext i; fin_cases i <;> simp [maxStore]
    · simp [maxStore]
  have h3 : (clear (1 : Fin 11)).Executes g (maxStore item idx pos 0 rest [])
      (maxStore item 0 pos 0 rest []) (idx+1) := by
    convert clear_executes g (1 : Fin 11) (maxStore item idx pos 0 rest []) using 1
    · funext i; fin_cases i <;> rfl
    · simp [maxStore]
  have h4 : (copyOn (2 : Fin 11) 1 10 (by decide) (by decide) (by decide)).Executes g
      (maxStore item 0 pos 0 rest []) (maxStore item pos pos 0 rest []) (5*pos+2) := by
    convert copyOn_executes g (2 : Fin 11) 1 10 (by decide) (by decide) (by decide)
      (maxStore item 0 pos 0 rest []) rfl using 1
    · funext i; fin_cases i <;> simp [maxStore]
    · simp [maxStore]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> omega

 theorem maxDecision_executes (g : BitString → ℕ) (best idx pos item : ℕ) (rest : BitString) :
    ∃ t, maxDecision.Executes g (maxStore best idx pos item rest [decide (best ≤ item)])
      (maxStore (keepBetter (best,idx) (item,pos)).1 (keepBetter (best,idx) (item,pos)).2 pos 0 rest []) t ∧
      t ≤ best+6*item+idx+5*pos+17 := by
  by_cases h : best ≤ item
  · refine ⟨best+6*item+idx+5*pos+15+2,?_,by omega⟩
    simp only [h,decide_true,keepBetter,if_pos]
    apply branchPop_true _ _ _ _ g rfl
    convert maxReplace_executes g best idx pos item rest using 1
    funext i; fin_cases i <;> rfl
  · refine ⟨item+1+2,?_,by omega⟩
    simp only [h,decide_false,keepBetter,if_neg]
    apply branchPop_false _ _ _ _ g rfl
    convert clear_executes g (4 : Fin 11) (maxStore best idx pos item rest []) using 1
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · simp [maxStore]

 theorem maxBody_executes (g : BitString → ℕ) (best idx pos item : ℕ) (rest : BitString) :
    ∃ t, maxBody.Executes g
      (maxStore best idx pos 0 (pairBits (List.replicate item true) rest) [])
      (maxStore (keepBetter (best,idx) (item,pos)).1 (keepBetter (best,idx) (item,pos)).2 (pos+1) 0 rest []) t ∧
      t+2 ≤ 19*item+9*best+idx+5*pos+50 := by
  have hp := maxParse_executes g best idx pos item rest
  have hclear : (clear (5 : Fin 11)).Executes g (maxStore best idx pos item rest [true])
      (maxStore best idx pos item rest []) 2 := by
    convert clear_executes g (5 : Fin 11) (maxStore best idx pos item rest [true]) using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨tc,hc,hbc⟩ := maxCompare_executes g best idx pos item rest
  obtain ⟨td,hd,hbd⟩ := maxDecision_executes g best idx pos item rest
  have hi : (push (2 : Fin 11) true).Executes g
      (maxStore (keepBetter (best,idx) (item,pos)).1 (keepBetter (best,idx) (item,pos)).2 pos 0 rest [])
      (maxStore (keepBetter (best,idx) (item,pos)).1 (keepBetter (best,idx) (item,pos)).2 (pos+1) 0 rest []) 1 := by
    convert push_executes g (2 : Fin 11) true
      (maxStore (keepBetter (best,idx) (item,pos)).1 (keepBetter (best,idx) (item,pos)).2 pos 0 rest []) using 1
    funext i; fin_cases i <;> simp [maxStore,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hclear (seq_executes _ _ g hc (seq_executes _ _ g hd hi))),?_⟩
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
