import HiddenCircuits.Circuit.Runtime.SourceHardness

/-! Standalone signed WordEval hardness. The natural oracle output is the binary
value of the sign/magnitude word; a fixed one-port program restores positive zero.
This is a representation of an integer-valued arithmetic oracle, not a #P-membership
claim for its potentially negative mathematical value. -/
namespace HiddenCircuits.Circuit.Runtime.WordEvalOracle
open Complexity OracleBlock BinaryArithmetic Polynomial

def signedCode (z : ℤ) : ℕ := BinaryArithmetic.value (signedBits z)
def oracleSpec (g : BitString→ℕ) : Prop := ∀w : WordInstance,g (wordBits w)=signedCode w.value.num
noncomputable def problem (xs : BitString) : ℕ :=
  match decodeWord xs with
  | none=>0
  | some w=>signedCode w.value.num
lemma problem_spec : oracleSpec problem := by intro w;simp [problem]
lemma code_encode (z : ℤ) : Computability.encodeNat (signedCode z)=if z=0 then [] else signedBits z := by
  by_cases hz:z=0
  · subst z;rfl
  · rw [if_neg hz]
    apply (canonical_eq_encode ?_).symm
    refine ⟨canonical_encodeNat _,?_⟩
    intro he
    have hn : z.natAbs=0 := (encodeNat_eq_nil_iff _).mp he
    exact False.elim (hz (Int.natAbs_eq_zero.mp hn))
lemma code_length (z : ℤ) : (Computability.encodeNat (signedCode z)).length≤(signedBits z).length := by
  rw [code_encode]
  split_ifs <;> simp
lemma word_integer (w : WordInstance) : w.value=(w.value.num:ℚ) := by
  obtain ⟨z,hz,hb⟩:=word_value_bits_input w
  rw [hz]
  simp
lemma word_bits_bound (w : WordInstance) : (signedBits w.value.num).length≤14*(wordBits w).length^5 := by
  obtain ⟨z,hz,hb⟩:=word_value_bits_input w
  simpa [hz,signedBits,encodeNat_length] using hb

noncomputable def restore : OracleBlock 0 := branchPop 0 (push 0 false) (push 0 false) (push 0 true)
noncomputable def program : OracleBlock 0 := seq (query 0 0) restore
noncomputable def time : Polynomial ℕ := 14*X^5+X+6

def state (xs : BitString) : Store 0 := fun _=>xs
lemma restore_executes (g : BitString→ℕ) (z : ℤ) :
    restore.Executes g (state (Computability.encodeNat (signedCode z))) (state (signedBits z)) 3 := by
  rw [code_encode]
  by_cases hz:z=0
  · subst z
    simp only [if_pos rfl]
    apply branchPop_empty 0 _ _ _ g (by rfl)
    convert push_executes g (0:Fin 1) false (state []) using 1
    funext i;fin_cases i;rfl
  · rw [if_neg hz]
    cases hneg:negative z with
    | false =>
      apply branchPop_false 0 _ _ _ g (rest:=Computability.encodeNat z.natAbs)
      · simp only [state,signedBits,hneg]
      · convert push_executes g (0:Fin 1) false (state (Computability.encodeNat z.natAbs)) using 1
        · funext i;fin_cases i;rfl
        · funext i;fin_cases i;simp [state,signedBits,hneg]
    | true =>
      apply branchPop_true 0 _ _ _ g (rest:=Computability.encodeNat z.natAbs)
      · simp only [state,signedBits,hneg]
      · convert push_executes g (0:Fin 1) true (state (Computability.encodeNat z.natAbs)) using 1
        · funext i;fin_cases i;rfl
        · funext i;fin_cases i;simp [state,signedBits,hneg]
lemma solverSpec (g : BitString→ℕ) (hg : oracleSpec g) : SourceWordCall.WordSolverSpec program g time := by
  intro w
  have hq : (query (0:Fin 1) 0).Executes g (state (wordBits w))
      (state (Computability.encodeNat (signedCode w.value.num)))
      (1+(wordBits w).length+(Computability.encodeNat (signedCode w.value.num)).length) := by
    convert query_executes g (0:Fin 1) 0 (state (wordBits w)) using 1
    · funext i;fin_cases i;simp [state,OracleMachine.answerBits,hg w]
    · simp [state,OracleMachine.answerBits,hg w]
  have he:=seq_executes _ _ g hq (restore_executes g w.value.num)
  refine ⟨w.value.num,1+(wordBits w).length+(Computability.encodeNat (signedCode w.value.num)).length+3+2,?_,word_integer w,?_⟩
  · convert he using 1 <;> funext i <;> fin_cases i <;> rfl
  · have hc:=code_length w.value.num
    have hb:=word_bits_bound w
    simp only [time,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X]
    omega

theorem sharpPHard_of_oracle (g : BitString→ℕ) (hg : oracleSpec g) : SharpPHard g :=
  SourceReduction.sharpPHard program g time (solverSpec g hg)
theorem wordEval_sharpPHard : SharpPHard problem := sharpPHard_of_oracle problem problem_spec
end HiddenCircuits.Circuit.Runtime.WordEvalOracle
