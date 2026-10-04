import HiddenCircuits.Complexity.FamilyEmitter

/-! A real variable-height row loop for the verifier-to-CNF emitter. Unary
positions increase by actual pushes while the remaining-height stack is popped. -/
namespace HiddenCircuits.Complexity.RowEmitter
open OracleBlock TM2BooleanEncoding Polynomial

noncomputable def stackBits (M : Turing.FinTM2) (base nextBase : ℕ) : ℕ → ℕ → BitString
  | _, 0 => []
  | j, r+1 => FamilyEmitter.bits M (FamilyEmitter.symbols M) j r base nextBase ++
      stackBits M base nextBase (j+1) r

noncomputable def stackLoop (M : Turing.FinTM2) : OracleBlock 7 :=
  whilePop 5 (FamilyEmitter.symbolBody M) (FamilyEmitter.symbolBody M)

lemma pop_remaining (j base nextBase r : ℕ) (stream : BitString) :
    Function.update (LocalClauseEmitter.state j base nextBase 0 0 0 (r+1) stream) 5 (List.replicate r true) =
      LocalClauseEmitter.state j base nextBase 0 0 0 r stream := by
  funext i;fin_cases i <;> rfl

/-- The loop's complete operational derivation and polynomial bound. Every body
is the already verified actual finite symbol-family emitter. -/
theorem stackLoop_execution (g : BitString → ℕ) (M : Turing.FinTM2) (j r base nextBase : ℕ) (stream : BitString) :
    ∃ cost, WhileExecution (5 : Fin 8) (FamilyEmitter.symbolBody M) (FamilyEmitter.symbolBody M) g
      (LocalClauseEmitter.state j base nextBase 0 0 0 r stream)
      (LocalClauseEmitter.state (j+r) base nextBase 0 0 0 0 ((stackBits M base nextBase j r).reverse++stream)) cost ∧
      cost ≤ r*((FamilyEmitter.time M (FamilyEmitter.symbols M)).eval (j+r+base+nextBase)+5)+1 := by
  induction r generalizing j stream with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [stackBits] using WhileExecution.empty (LocalClauseEmitter.state j base nextBase 0 0 0 0 stream) rfl
  | succ r ih =>
    obtain ⟨cb,hb,hbb⟩ := FamilyEmitter.symbolBody_executes g M j r base nextBase stream
    obtain ⟨ct,ht,hbt⟩ := ih (j+1) ((FamilyEmitter.bits M (FamilyEmitter.symbols M) j r base nextBase).reverse++stream)
    have hbody : (FamilyEmitter.symbolBody M).Executes g
        (Function.update (LocalClauseEmitter.state j base nextBase 0 0 0 (r+1) stream) 5 (List.replicate r true))
        (LocalClauseEmitter.state (j+1) base nextBase 0 0 0 r
          ((FamilyEmitter.bits M (FamilyEmitter.symbols M) j r base nextBase).reverse++stream)) cb := by
      rwa [pop_remaining]
    have hs : (LocalClauseEmitter.state j base nextBase 0 0 0 (r+1) stream) 5 = true::List.replicate r true := rfl
    have h := WhileExecution.one hs hbody ht
    refine ⟨1+cb+1+ct,?_,?_⟩
    · convert h using 1 <;> simp [stackBits,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · have hm := polynomial_nat_eval_mono (FamilyEmitter.time M (FamilyEmitter.symbols M))
        (show j+r+base+nextBase ≤ j+(r+1)+base+nextBase by omega)
      dsimp only at hm
      rw [show j+1+r+base+nextBase=j+(r+1)+base+nextBase by omega] at hbt
      nlinarith

theorem stackLoop_executes (g : BitString → ℕ) (M : Turing.FinTM2) (j r base nextBase : ℕ) (stream : BitString) :
    ∃ cost, (stackLoop M).Executes g (LocalClauseEmitter.state j base nextBase 0 0 0 r stream)
      (LocalClauseEmitter.state (j+r) base nextBase 0 0 0 0 ((stackBits M base nextBase j r).reverse++stream)) cost ∧
      cost ≤ r*((FamilyEmitter.time M (FamilyEmitter.symbols M)).eval (j+r+base+nextBase)+5)+1 := by
  obtain ⟨cost,hc,hb⟩ := stackLoop_execution g M j r base nextBase stream
  exact ⟨cost,whilePop_executes _ _ _ g hc,hb⟩

noncomputable def bits (M : Turing.FinTM2) (height base nextBase : ℕ) : BitString :=
  FamilyEmitter.bits M (FamilyEmitter.controls M) 0 (height-1) base nextBase ++ stackBits M base nextBase 0 height

noncomputable def positiveBody (M : Turing.FinTM2) : OracleBlock 7 :=
  seq (FamilyEmitter.program M (FamilyEmitter.controls M))
    (seq (push 5 true) (seq (stackLoop M) (clear 0)))

/-- Empty height is a harmless unused branch. Actual verifier heights are positive. -/
noncomputable def program (M : Turing.FinTM2) : OracleBlock 7 :=
  branchPop 5 skip (positiveBody M) (positiveBody M)

noncomputable def time (M : Turing.FinTM2) : Polynomial ℕ :=
  FamilyEmitter.time M (FamilyEmitter.controls M)+X*(FamilyEmitter.time M (FamilyEmitter.symbols M)+6)+11

/-- One actual entire row is emitted, including all control and stack cells.
The position and remaining-height registers both finish empty. -/
theorem program_executes (g : BitString → ℕ) (M : Turing.FinTM2) (height base nextBase : ℕ)
    (hheight : 0<height) (stream : BitString) :
    ∃ cost, (program M).Executes g (LocalClauseEmitter.state 0 base nextBase 0 0 0 height stream)
      (LocalClauseEmitter.state 0 base nextBase 0 0 0 0 ((bits M height base nextBase).reverse++stream)) cost ∧
      cost ≤ (time M).eval (height+base+nextBase) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : height ≠ 0)
  let ctrl := FamilyEmitter.bits M (FamilyEmitter.controls M) 0 r base nextBase
  let acc := ctrl.reverse++stream
  obtain ⟨cc,hc,hbc⟩ := FamilyEmitter.program_executes g M (FamilyEmitter.controls M) 0 r base nextBase stream
  have hp : (push (5 : Fin 8) true).Executes g (LocalClauseEmitter.state 0 base nextBase 0 0 0 r acc)
      (LocalClauseEmitter.state 0 base nextBase 0 0 0 (r+1) acc) 1 := by
    have h := push_executes g (5 : Fin 8) true (LocalClauseEmitter.state 0 base nextBase 0 0 0 r acc)
    convert h using 1
    funext i;fin_cases i <;> simp [LocalClauseEmitter.state,List.replicate_succ]
  obtain ⟨cs,hs,hbs⟩ := stackLoop_executes g M 0 (r+1) base nextBase acc
  simp only [Nat.zero_add] at hs hbs
  have hclear : (clear (0 : Fin 8)).Executes g
      (LocalClauseEmitter.state (r+1) base nextBase 0 0 0 0 ((stackBits M base nextBase 0 (r+1)).reverse++acc))
      (LocalClauseEmitter.state 0 base nextBase 0 0 0 0 ((stackBits M base nextBase 0 (r+1)).reverse++acc)) (r+2) := by
    have h := clear_executes g (0 : Fin 8)
      (LocalClauseEmitter.state (r+1) base nextBase 0 0 0 0 ((stackBits M base nextBase 0 (r+1)).reverse++acc))
    convert h using 1
    · funext i;fin_cases i <;> simp [LocalClauseEmitter.state]
    · simp [LocalClauseEmitter.state]
  have hb := seq_executes _ _ g hc (seq_executes _ _ g hp (seq_executes _ _ g hs hclear))
  have hbody : (positiveBody M).Executes g
      (Function.update (LocalClauseEmitter.state 0 base nextBase 0 0 0 (r+1) stream) 5 (List.replicate r true))
      (LocalClauseEmitter.state 0 base nextBase 0 0 0 0 ((bits M (r+1) base nextBase).reverse++stream))
      (cc+(1+(cs+(r+2)+2)+2)+2) := by
    simpa [pop_remaining,bits,acc,ctrl,List.reverse_append,List.append_assoc] using hb
  have hout := branchPop_true (5 : Fin 8) skip (positiveBody M) (positiveBody M) g
    (s := LocalClauseEmitter.state 0 base nextBase 0 0 0 (r+1) stream) rfl hbody
  refine ⟨_,hout,?_⟩
  have hm := polynomial_nat_eval_mono (FamilyEmitter.time M (FamilyEmitter.controls M))
    (show 0+r+base+nextBase ≤ r+1+base+nextBase by omega)
  dsimp only at hm
  have hsTime := Nat.mul_le_mul_right ((FamilyEmitter.time M (FamilyEmitter.symbols M)).eval (r+1+base+nextBase)+6)
    (show r+1 ≤ r+1+base+nextBase by omega)
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  nlinarith

lemma program_queryFree (M : Turing.FinTM2) : (program M).QueryFree := by
  have hb : (positiveBody M).QueryFree :=
    seq_queryFree _ _ (FamilyEmitter.program_queryFree _ _)
      (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _
        (whilePop_queryFree _ _ _ (FamilyEmitter.symbolBody_queryFree _) (FamilyEmitter.symbolBody_queryFree _))
        (clear_queryFree _)))
  exact branchPop_queryFree _ _ _ _ skip_queryFree hb hb

end HiddenCircuits.Complexity.RowEmitter
