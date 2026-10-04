import HiddenCircuits.Approximation.SelfReduction.Runtime.MatchTallyLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.UnaryEmit

/-! One finite loop body counts a target in a serialized sample group, emits its
unary count, and preserves the target plus the remaining sample groups. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def groupStore (target work source out : BitString) (count : ℕ) (flag : BitString) : Store 13 := fun i =>
  if i.val=0 then target else if i.val=1 then work else if i.val=2 then List.replicate count true
  else if i.val=10 then source else if i.val=11 then out else if i.val=13 then flag else []

def groupParsePorts : Fin 4 ↪ Fin 14 where
  toFun i := if i.val=0 then 10 else if i.val=1 then 1 else if i.val=2 then 12 else 13
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def groupTallyPorts : Fin 10 ↪ Fin 14 where
  toFun i := i.castAdd 4
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 14 => x.val) h)

noncomputable def groupParse : OracleBlock 13 := GraphVerifier.Runtime.unpairOn groupParsePorts
noncomputable def groupTally : OracleBlock 13 := rename occurrenceTally groupTallyPorts
noncomputable def groupBody : OracleBlock 13 :=
  seq groupParse (seq (clear 13) (seq groupTally (emitUnaryReversed 2 11)))

 theorem groupParse_executes (g : BitString → ℕ) (target word rest out : BitString) :
    groupParse.Executes g (groupStore target [] (pairBits word rest) out 0 [])
      (groupStore target word rest out 0 [true]) (5*word.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes groupParsePorts g
    (groupStore target [] (pairBits word rest) out 0 []) (groupStore target word rest out 0 [true])
    (pairBits word rest)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro j hj; fin_cases j; all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair,BinaryArithmetic.pair_parse_cost]
  omega

 theorem groupBody_executes (g : BitString → ℕ) (target rest out : BitString) (xs : List BitString)
    (B : ℕ) (hxs : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t, groupBody.Executes g (groupStore target [] (pairBits (encodeBitList xs) rest) out 0 [])
      (groupStore target [] rest
        ((true::pairBits (List.replicate (wordOccurrences target xs) true) []).reverse++out) 0 []) t ∧
      t+2 ≤ 5*(encodeBitList xs).length+xs.length*(60*(B+target.length+1))+9*xs.length+21 := by
  have hp := groupParse_executes g target (encodeBitList xs) rest out
  have hc : (clear (13 : Fin 14)).Executes g (groupStore target (encodeBitList xs) rest out 0 [true])
      (groupStore target (encodeBitList xs) rest out 0 []) 2 := by
    convert clear_executes g (13 : Fin 14) (groupStore target (encodeBitList xs) rest out 0 [true]) using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨tt,ht,hbt⟩ := occurrenceTally_executes g target xs 0 B hxs
  have hcall : groupTally.Executes g (groupStore target (encodeBitList xs) rest out 0 [])
      (groupStore target [] rest out (wordOccurrences target xs) []) tt := by
    apply rename_executes_to occurrenceTally groupTallyPorts g ht
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [groupTallyPorts,groupStore,matchStore]
    · intro j hj; fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) | exact False.elim (hj 2 rfl)
  have he : (emitUnaryReversed (2 : Fin 14) 11).Executes g
      (groupStore target [] rest out (wordOccurrences target xs) [])
      (groupStore target [] rest ((true::pairBits (List.replicate (wordOccurrences target xs) true) []).reverse++out) 0 [])
      (9*wordOccurrences target xs+7) := by
    convert emitUnaryReversed_executes g (2 : Fin 14) 11 (by decide)
      (groupStore target [] rest out (wordOccurrences target xs) []) using 1
    · funext i; fin_cases i <;> simp [groupStore]
    · simp [groupStore]
  have hn : wordOccurrences target xs ≤ xs.length := List.countP_le_length
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hcall he)),?_⟩
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
