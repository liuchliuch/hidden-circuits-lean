import HiddenCircuits.Complexity.OracleBlockLift

/-! Syntactic oracle-freedom of the actual compiled structured blocks. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

lemma wireMachine_queryFree {b c : ℕ} (blocks : Fin b → OracleBlock k)
    (control : Fin c → OracleInstr (k+1) (Fintype.card (WireLabel blocks c)))
    (continuation : Fin b → WireLabel blocks c) (start : WireLabel blocks c)
    (hb : ∀ i, (blocks i).QueryFree)
    (hc : ∀ q i o next, control q ≠ .query i o next) :
    (wireMachine blocks control continuation start).QueryFree := by
  intro q i o next h
  change (match (wireEquiv blocks).symm q with
    | .inl l => control l
    | .inr ⟨j,l⟩ => if l = (blocks j).exit then .jump (wireEquiv blocks (continuation j))
      else OracleInstr.map id (blockLabel blocks j) ((blocks j).code l)) = .query i o next at h
  split at h
  · exact hc _ _ _ _ h
  · rename_i j l hlabel
    by_cases he : l = (blocks j).exit
    · rw [if_pos he] at h;cases h
    · rw [if_neg he] at h
      exact instr_map_noquery ((blocks j).code l) id (blockLabel blocks j) ((hb j) l) i o next h

lemma skip_queryFree : (skip (k := k)).QueryFree := by
  intro q i o next h
  fin_cases q <;> cases h

lemma push_queryFree (stack : Fin (k+1)) (bit : Bool) : (push stack bit).QueryFree := by
  intro q i o next h
  fin_cases q <;> cases h

lemma seq_queryFree (B C : OracleBlock k) (hB : B.QueryFree) (hC : C.QueryFree) : (seq B C).QueryFree := by
  apply wireMachine_queryFree (twoBlocks B C) (fun _ => .halt) (seqContinuation B C) (.inr ⟨0,B.start⟩)
  · intro i;fin_cases i
    · exact hB
    · exact hC
  · intro q i o next h;cases h

lemma whilePop_queryFree (stack : Fin (k+1)) (B C : OracleBlock k)
    (hB : B.QueryFree) (hC : C.QueryFree) : (whilePop stack B C).QueryFree := by
  apply wireMachine_queryFree (twoBlocks B C) (loopControl stack B C) (fun _ => .inl 0) (.inl 0)
  · intro i;fin_cases i
    · exact hB
    · exact hC
  · intro q i o next h;fin_cases q <;> cases h

lemma branchPop_queryFree (stack : Fin (k+1)) (E B C : OracleBlock k)
    (hE : E.QueryFree) (hB : B.QueryFree) (hC : C.QueryFree) : (branchPop stack E B C).QueryFree := by
  apply wireMachine_queryFree (threeBlocks E B C) (branchControl stack E B C) (fun _ => .inl 1) (.inl 0)
  · intro i;fin_cases i
    · exact hE
    · exact hB
    · exact hC
  · intro q i o next h;fin_cases q <;> cases h

end HiddenCircuits.Complexity.OracleBlock
