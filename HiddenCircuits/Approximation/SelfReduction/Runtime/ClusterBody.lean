import HiddenCircuits.Approximation.SelfReduction.Runtime.RadiusTest
import HiddenCircuits.Approximation.SelfReduction.Runtime.ListLookup

/-! A literal scan step
parses an encoded unary value and increments a physical neighborhood counter. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
set_option maxHeartbeats 800000

def clusterStore (target radius count item : ℕ) (stream parseFlag testFlag : BitString) : Store 12 := fun i =>
  if i.val=0 then List.replicate target true else if i.val=1 then List.replicate radius true
  else if i.val=2 then List.replicate count true else if i.val=3 then stream
  else if i.val=4 then List.replicate item true else if i.val=5 then testFlag
  else if i.val=12 then parseFlag else []

def clusterParseEmbedding : Fin 4 ↪ Fin 13 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 4 else if i.val=2 then 11 else 12
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def clusterTestEmbedding : Fin 8 ↪ Fin 13 where
  toFun i := if i.val<2 then ⟨i.val,by omega⟩ else ⟨i.val+2,by omega⟩
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def clusterParse : OracleBlock 12 := GraphVerifier.Runtime.unpairOn clusterParseEmbedding
noncomputable def clusterTest : OracleBlock 12 := rename radiusTest clusterTestEmbedding
noncomputable def clusterIncrement : OracleBlock 12 := branchPop 5 skip skip (push 2 true)
noncomputable def clusterBody : OracleBlock 12 :=
  seq clusterParse (seq (clear 12) (seq clusterTest (seq clusterIncrement (clear 4))))

theorem clusterParse_executes (g : BitString → ℕ) (target radius count item : ℕ) (rest : BitString) :
    clusterParse.Executes g
      (clusterStore target radius count 0 (pairBits (List.replicate item true) rest) [] [])
      (clusterStore target radius count item rest [true] []) (5*item+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes clusterParseEmbedding g
    (clusterStore target radius count 0 (pairBits (List.replicate item true) rest) [] [])
    (clusterStore target radius count item rest [true] []) (pairBits (List.replicate item true) rest)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj; fin_cases j; all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,BinaryArithmetic.pair_parse_cost]
  omega

theorem clusterTest_executes (g : BitString → ℕ) (target radius count item : ℕ) (rest : BitString) :
    ∃ t, clusterTest.Executes g (clusterStore target radius count item rest [] [])
      (clusterStore target radius count item rest [] [decide (item ≤ target+radius ∧ target ≤ item+radius)]) t ∧
      t  ≤  50*(target+radius+item+1) := by
  obtain ⟨t,ht,hb⟩ := radiusTest_executes g target radius item
  refine ⟨t,?_,hb⟩
  apply rename_executes_to radiusTest clusterTestEmbedding g ht
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro j hj; fin_cases j
    all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl)

theorem clusterIncrement_executes (g : BitString → ℕ) (target radius count item : ℕ) (rest : BitString) (ok : Bool) :
    clusterIncrement.Executes g (clusterStore target radius count item rest [] [ok])
      (clusterStore target radius (count+if ok then 1 else 0) item rest [] []) 3 := by
  cases ok with
  | false =>
    apply branchPop_false _ _ _ _ g rfl
    convert skip_executes g (clusterStore target radius count item rest [] []) using 1
    funext i; fin_cases i <;> rfl
  | true =>
    apply branchPop_true _ _ _ _ g rfl
    convert push_executes g (2 : Fin 13) true (clusterStore target radius count item rest [] []) using 1
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [clusterStore,List.replicate_succ]

theorem clusterBody_executes (g : BitString → ℕ) (target radius count item : ℕ) (rest : BitString) :
    ∃ t, clusterBody.Executes g
      (clusterStore target radius count 0 (pairBits (List.replicate item true) rest) [] [])
      (clusterStore target radius (count+if item ≤ target+radius ∧ target ≤ item+radius then 1 else 0) 0 rest [] []) t ∧
      t+2  ≤  80*(item+target+radius+1) := by
  have hp := clusterParse_executes g target radius count item rest
  have hc : (clear (12 : Fin 13)).Executes g (clusterStore target radius count item rest [true] [])
      (clusterStore target radius count item rest [] []) 2 := by
    convert clear_executes g (12 : Fin 13) (clusterStore target radius count item rest [true] []) using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨tt,ht,hbt⟩ := clusterTest_executes g target radius count item rest
  have hi := clusterIncrement_executes g target radius count item rest (decide (item ≤ target+radius ∧ target ≤ item+radius))
  simp only [Bool.decide_iff] at hi
  have hd : (clear (4 : Fin 13)).Executes g
      (clusterStore target radius (count+if item ≤ target+radius ∧ target ≤ item+radius then 1 else 0) item rest [] [])
      (clusterStore target radius (count+if item ≤ target+radius ∧ target ≤ item+radius then 1 else 0) 0 rest [] []) (item+1) := by
    convert clear_executes g (4 : Fin 13)
      (clusterStore target radius (count+if item ≤ target+radius ∧ target ≤ item+radius then 1 else 0) item rest [] []) using 1
    · funext i; fin_cases i <;> rfl
    · simp [clusterStore]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g ht (seq_executes _ _ g hi hd))),?_⟩
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
