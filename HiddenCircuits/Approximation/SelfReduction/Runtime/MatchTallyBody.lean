import HiddenCircuits.Approximation.SelfReduction.Runtime.ListLookup
import HiddenCircuits.Complexity.CNFCloneEmitter.WordEquality

/-! Real empirical occurrence counting on encoded sample-result words. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def matchStore (target stream : BitString) (count : ℕ) (item parseFlag matchFlag : BitString) : Store 9 := fun i =>
  if i.val=0 then target else if i.val=1 then stream else if i.val=2 then List.replicate count true
  else if i.val=3 then item else if i.val=5 then parseFlag else if i.val=8 then matchFlag else []

def matchParseEmbedding : Fin 4 ↪ Fin 10 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 3 else if i.val=2 then 4 else 5
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def matchCompareEmbedding : Fin 3 ↪ Fin 10 where
  toFun i := ⟨i.val+6,by omega⟩
  inj' := by intro i j h; apply Fin.ext; have hh := congrArg (fun x : Fin 10 => x.val) h; simp at hh; omega

noncomputable def matchParse : OracleBlock 9 := GraphVerifier.Runtime.unpairOn matchParseEmbedding
noncomputable def matchCompare : OracleBlock 9 :=
  seq (copyOn 0 6 9 (by decide) (by decide) (by decide))
    (seq (copyOn 3 7 9 (by decide) (by decide) (by decide))
      (seq (push 8 true) (rename CNFCloneEmitter.WordEquality.program matchCompareEmbedding)))
noncomputable def matchIncrement : OracleBlock 9 := branchPop 8 skip skip (push 2 true)
noncomputable def matchBody : OracleBlock 9 :=
  seq matchParse (seq (clear 5) (seq matchCompare (seq matchIncrement (clear 3))))

 theorem matchParse_executes (g : BitString → ℕ) (target word rest : BitString) (count : ℕ) :
    matchParse.Executes g (matchStore target (pairBits word rest) count [] [] [])
      (matchStore target rest count word [true] []) (5*word.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes matchParseEmbedding g
    (matchStore target (pairBits word rest) count [] [] []) (matchStore target rest count word [true] [])
    (pairBits word rest)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj; fin_cases j; all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair, BinaryArithmetic.pair_parse_cost]
  omega

 theorem matchCompare_executes (g : BitString → ℕ) (target word rest : BitString) (count : ℕ) :
    ∃ t, matchCompare.Executes g (matchStore target rest count word [] [])
      (matchStore target rest count word [] [decide (target=word)]) t ∧
      t ≤ 15*(target.length+word.length)+24 := by
  let s := matchStore target rest count word [] []
  let s1 := Function.update s (6 : Fin 10) target
  let s2 := Function.update s1 (7 : Fin 10) word
  let s3 := Function.update s2 (8 : Fin 10) [true]
  have h1 : (copyOn (0 : Fin 10) 6 9 (by decide) (by decide) (by decide)).Executes g s s1 (5*target.length+2) := by
    convert copyOn_executes g (0 : Fin 10) 6 9 (by decide) (by decide) (by decide) s rfl using 1
    funext i; fin_cases i <;> simp [s,s1,matchStore]
  have h2 : (copyOn (3 : Fin 10) 7 9 (by decide) (by decide) (by decide)).Executes g s1 s2 (5*word.length+2) := by
    convert copyOn_executes g (3 : Fin 10) 7 9 (by decide) (by decide) (by decide) s1 rfl using 1
    funext i; fin_cases i <;> simp [s,s1,s2,matchStore]
  have h3 : (push (8 : Fin 10) true).Executes g s2 s3 1 := by
    convert push_executes g (8 : Fin 10) true s2 using 1
  obtain ⟨tc,hc,hbc⟩ := CNFCloneEmitter.WordEquality.program_executes g target word
  have h4 : (rename CNFCloneEmitter.WordEquality.program matchCompareEmbedding).Executes g s3
      (matchStore target rest count word [] [decide (target=word)]) tc := by
    apply rename_executes_to _ matchCompareEmbedding g hc
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  omega

 theorem matchIncrement_executes (g : BitString → ℕ) (target word rest : BitString) (count : ℕ) (ok : Bool) :
    matchIncrement.Executes g (matchStore target rest count word [] [ok])
      (matchStore target rest (count + if ok then 1 else 0) word [] []) 3 := by
  cases ok with
  | false =>
    apply branchPop_false _ _ _ _ g rfl
    convert skip_executes g (matchStore target rest count word [] []) using 1
    funext i; fin_cases i <;> rfl
  | true =>
    apply branchPop_true _ _ _ _ g rfl
    convert push_executes g (2 : Fin 10) true (matchStore target rest count word [] []) using 1
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [matchStore,List.replicate_succ]

 theorem matchBody_executes (g : BitString → ℕ) (target word rest : BitString) (count : ℕ) :
    ∃ t, matchBody.Executes g (matchStore target (pairBits word rest) count [] [] [])
      (matchStore target rest (count + if target=word then 1 else 0) [] [] []) t ∧
      t+2 ≤ 21*word.length+15*target.length+43 := by
  have hp := matchParse_executes g target word rest count
  have hc : (clear (5 : Fin 10)).Executes g (matchStore target rest count word [true] [])
      (matchStore target rest count word [] []) 2 := by
    convert clear_executes g (5 : Fin 10) (matchStore target rest count word [true] []) using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨tt,ht,hbt⟩ := matchCompare_executes g target word rest count
  have hi := matchIncrement_executes g target word rest count (decide (target=word))
  simp only [Bool.decide_iff] at hi
  have hclear : (clear (3 : Fin 10)).Executes g
      (matchStore target rest (count + if target=word then 1 else 0) word [] [])
      (matchStore target rest (count + if target=word then 1 else 0) [] [] []) (word.length+1) := by
    convert clear_executes g (3 : Fin 10)
      (matchStore target rest (count + if target=word then 1 else 0) word [] []) using 1
    funext i; fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g ht
    (seq_executes _ _ g hi hclear))),?_⟩
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
