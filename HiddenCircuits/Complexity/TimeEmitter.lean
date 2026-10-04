import HiddenCircuits.Complexity.RowEmitter

/-! Actual nested time/height iteration of the uniform tableau emitter. Master
height and cell count are preserved; each time step updates both unary row bases. -/
namespace HiddenCircuits.Complexity.TimeEmitter
open OracleBlock TM2BooleanEncoding Polynomial

/-- Row registers0..7, unary remaining time8, master height9 and cell count10. -/
def state (position base nextBase remaining clock height cells : ℕ) (stream : BitString) : Store 10 := fun i =>
  if i.val=6 then stream else List.replicate
    (if i.val=0 then position else if i.val=1 then base else if i.val=5 then remaining
      else if i.val=7 then nextBase else if i.val=8 then clock else if i.val=9 then height
      else if i.val=10 then cells else 0) true

noncomputable def rowProgram (M : Turing.FinTM2) : OracleBlock 10 :=
  rename (RowEmitter.program M) (Fin.castAddEmb 3)
noncomputable def copyHeight : OracleBlock 10 := copyOn 9 5 4 (by decide) (by decide) (by decide)
noncomputable def advanceBase : OracleBlock 10 := copyOn 10 1 4 (by decide) (by decide) (by decide)
noncomputable def advanceNext : OracleBlock 10 := copyOn 10 7 4 (by decide) (by decide) (by decide)
noncomputable def body (M : Turing.FinTM2) : OracleBlock 10 :=
  seq copyHeight (seq (rowProgram M) (seq advanceBase advanceNext))

theorem rowProgram_executes (g : BitString → ℕ) (M : Turing.FinTM2) (base nextBase clock height cells : ℕ)
    (hheight : 0<height) (stream : BitString) :
    ∃ cost, (rowProgram M).Executes g (state 0 base nextBase height clock height cells stream)
      (state 0 base nextBase 0 clock height cells ((RowEmitter.bits M height base nextBase).reverse++stream)) cost ∧
      cost ≤ (RowEmitter.time M).eval (height+base+nextBase) := by
  obtain ⟨cost,hc,hb⟩ := RowEmitter.program_executes g M height base nextBase hheight stream
  refine ⟨cost,?_,hb⟩
  apply rename_executes_to _ (Fin.castAddEmb 3) g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact (hi 0 rfl).elim
    · exact (hi 1 rfl).elim
    · exact (hi 2 rfl).elim
    · exact (hi 3 rfl).elim
    · exact (hi 4 rfl).elim
    · exact (hi 5 rfl).elim
    · exact (hi 6 rfl).elim
    · exact (hi 7 rfl).elim
    · rfl
    · rfl
    · rfl

theorem body_executes (g : BitString → ℕ) (M : Turing.FinTM2) (base nextBase clock height cells : ℕ)
    (hheight : 0<height) (stream : BitString) :
    ∃ cost, (body M).Executes g (state 0 base nextBase 0 clock height cells stream)
      (state 0 (base+cells) (nextBase+cells) 0 clock height cells
        ((RowEmitter.bits M height base nextBase).reverse++stream)) cost ∧
      cost ≤ (RowEmitter.time M).eval (height+base+nextBase)+5*height+10*cells+12 := by
  have h₁ : copyHeight.Executes g (state 0 base nextBase 0 clock height cells stream)
      (state 0 base nextBase height clock height cells stream) (5*height+2) := by
    have h := copyOn_executes g (9 : Fin 11) 5 4 (by decide) (by decide) (by decide)
      (state 0 base nextBase 0 clock height cells stream) rfl
    convert h using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  obtain ⟨cr,hr,hbr⟩ := rowProgram_executes g M base nextBase clock height cells hheight stream
  let out := (RowEmitter.bits M height base nextBase).reverse++stream
  have h₂ : advanceBase.Executes g (state 0 base nextBase 0 clock height cells out)
      (state 0 (base+cells) nextBase 0 clock height cells out) (5*cells+2) := by
    have h := copyOn_executes g (10 : Fin 11) 1 4 (by decide) (by decide) (by decide)
      (state 0 base nextBase 0 clock height cells out) rfl
    convert h using 1
    · funext i;fin_cases i <;> simp [state,Nat.add_comm]
    · simp [state]
  have h₃ : advanceNext.Executes g (state 0 (base+cells) nextBase 0 clock height cells out)
      (state 0 (base+cells) (nextBase+cells) 0 clock height cells out) (5*cells+2) := by
    have h := copyOn_executes g (10 : Fin 11) 7 4 (by decide) (by decide) (by decide)
      (state 0 (base+cells) nextBase 0 clock height cells out) rfl
    convert h using 1
    · funext i;fin_cases i <;> simp [state,Nat.add_comm]
    · simp [state]
  have h := seq_executes _ _ g h₁ (seq_executes _ _ g hr (seq_executes _ _ g h₂ h₃))
  exact ⟨_,h,by omega⟩

noncomputable def bits (M : Turing.FinTM2) (height cells : ℕ) : ℕ → ℕ → ℕ → BitString
  | _, _, 0 => []
  | base, nextBase, t+1 => RowEmitter.bits M height base nextBase ++
      bits M height cells (base+cells) (nextBase+cells) t
noncomputable def program (M : Turing.FinTM2) : OracleBlock 10 := whilePop 8 (body M) (body M)

lemma pop_clock (base nextBase clock height cells : ℕ) (stream : BitString) :
    Function.update (state 0 base nextBase 0 (clock+1) height cells stream) 8 (List.replicate clock true) =
      state 0 base nextBase 0 clock height cells stream := by
  funext i;fin_cases i <;> rfl

/-- Every actual transition row is emitted, with an explicit polynomially
bounded operational derivation of the two nested loops. -/
theorem loop_execution (g : BitString → ℕ) (M : Turing.FinTM2) (base nextBase clock height cells : ℕ)
    (hheight : 0<height) (stream : BitString) :
    ∃ cost, WhileExecution (8 : Fin 11) (body M) (body M) g
      (state 0 base nextBase 0 clock height cells stream)
      (state 0 (base+clock*cells) (nextBase+clock*cells) 0 0 height cells
        ((bits M height cells base nextBase clock).reverse++stream)) cost ∧
      cost ≤ clock*((RowEmitter.time M).eval (height+base+nextBase+2*clock*cells)+5*height+10*cells+14)+1 := by
  induction clock generalizing base nextBase stream with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [bits] using WhileExecution.empty (state 0 base nextBase 0 0 height cells stream) rfl
  | succ clock ih =>
    obtain ⟨cb,hb,hbb⟩ := body_executes g M base nextBase clock height cells hheight stream
    obtain ⟨ct,ht,hbt⟩ := ih (base+cells) (nextBase+cells) ((RowEmitter.bits M height base nextBase).reverse++stream)
    have hbody : (body M).Executes g
        (Function.update (state 0 base nextBase 0 (clock+1) height cells stream) 8 (List.replicate clock true))
        (state 0 (base+cells) (nextBase+cells) 0 clock height cells
          ((RowEmitter.bits M height base nextBase).reverse++stream)) cb := by
      rwa [pop_clock]
    have hs : (state 0 base nextBase 0 (clock+1) height cells stream) 8 = true::List.replicate clock true := rfl
    have h := WhileExecution.one hs hbody ht
    refine ⟨1+cb+1+ct,?_,?_⟩
    · convert h using 1 <;> simp [bits,List.reverse_append,List.append_assoc,Nat.add_mul,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · have hm := polynomial_nat_eval_mono (RowEmitter.time M)
        (show height+base+nextBase ≤ height+base+nextBase+2*(clock+1)*cells by omega)
      dsimp only at hm
      rw [show height+(base+cells)+(nextBase+cells)+2*clock*cells =
        height+base+nextBase+2*(clock+1)*cells by ring] at hbt
      nlinarith

noncomputable def time (M : Turing.FinTM2) : Polynomial ℕ :=
  X*((RowEmitter.time M).comp (3*X+2*X^2)+15*X+14)+1

theorem program_executes (g : BitString → ℕ) (M : Turing.FinTM2) (base nextBase clock height cells : ℕ)
    (hheight : 0<height) (stream : BitString) :
    ∃ cost, (program M).Executes g (state 0 base nextBase 0 clock height cells stream)
      (state 0 (base+clock*cells) (nextBase+clock*cells) 0 0 height cells
        ((bits M height cells base nextBase clock).reverse++stream)) cost ∧
      cost ≤ (time M).eval (height+base+nextBase+clock+cells) := by
  obtain ⟨cost,hc,hb⟩ := loop_execution g M base nextBase clock height cells hheight stream
  refine ⟨cost,whilePop_executes _ _ _ g hc,hb.trans ?_⟩
  let n := height+base+nextBase+clock+cells
  have ht : clock ≤ n := by dsimp [n];omega
  have hcells : cells ≤ n := by dsimp [n];omega
  have hheight' : height ≤ n := by dsimp [n];omega
  have hprod := Nat.mul_le_mul ht hcells
  have harg : height+base+nextBase+2*clock*cells ≤ 3*n+2*n^2 := by dsimp [n] at *;nlinarith
  have hm := polynomial_nat_eval_mono (RowEmitter.time M) harg
  dsimp only at hm
  have hfactor : (RowEmitter.time M).eval (height+base+nextBase+2*clock*cells)+5*height+10*cells+14 ≤
      (RowEmitter.time M).eval (3*n+2*n^2)+15*n+14 := by omega
  have h := Nat.add_le_add_right (Nat.mul_le_mul ht hfactor) 1
  simpa only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_comp,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one] using h

lemma program_queryFree (M : Turing.FinTM2) : (program M).QueryFree := by
  have hb : (body M).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ (RowEmitter.program_queryFree _))
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _)))
  exact whilePop_queryFree _ _ _ hb hb

end HiddenCircuits.Complexity.TimeEmitter
