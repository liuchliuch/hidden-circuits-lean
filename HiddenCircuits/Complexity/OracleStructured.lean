import HiddenCircuits.Complexity.OracleBlocks

/-! Structured control flow compiled to actual finite bit-instruction code.
Each continuation has a counted jump; looping tests pop one real bit. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

def twoBlocks (B C : OracleBlock k) : Fin 2 → OracleBlock k := Fin.cases B (fun _ => C)

def seqContinuation (B C : OracleBlock k) : Fin 2 → WireLabel (twoBlocks B C) 1 :=
  Fin.cases (.inr ⟨1,C.start⟩) (fun _ => .inl 0)

noncomputable def seq (B C : OracleBlock k) : OracleBlock k where
  labelCount := Fintype.card (WireLabel (twoBlocks B C) 1)
  start := blockLabel (twoBlocks B C) 0 B.start
  exit := controlLabel (twoBlocks B C) (0 : Fin 1)
  code := (wireMachine (twoBlocks B C) (fun _ => .halt) (seqContinuation B C) (.inr ⟨0,B.start⟩)).code
  exit_halt := wireMachine_control _ _ _ _ _

/-- Sequencing has the actual cost of both blocks and two continuation jumps. -/
theorem seq_executes (B C : OracleBlock k) (g : BitString → ℕ) {s t u : Store k} {a b : ℕ}
    (hB : B.Executes g s t a) (hC : C.Executes g t u b) :
    (seq B C).Executes g s u (a+b+2) := by
  have h₁ := wireMachine_executes_continuation (twoBlocks B C) (fun _ => .halt)
    (seqContinuation B C) (.inr ⟨0,B.start⟩) 0 g hB
  have h₂ := wireMachine_executes_continuation (twoBlocks B C) (fun _ => .halt)
    (seqContinuation B C) (.inr ⟨0,B.start⟩) 1 g hC
  have h := h₁.trans h₂
  convert h using 1 <;> omega

noncomputable def loopControl (stack : Fin (k+1)) (B C : OracleBlock k) :
    Fin 2 → OracleInstr (k+1) (Fintype.card (WireLabel (twoBlocks B C) 2)) :=
  Fin.cases (.pop stack (controlLabel (twoBlocks B C) 1)
    (blockLabel (twoBlocks B C) 0 B.start) (blockLabel (twoBlocks B C) 1 C.start)) (fun _ => .halt)

/-- Repeatedly pop a bit, execute its corresponding branch, and test again. -/
noncomputable def whilePop (stack : Fin (k+1)) (B C : OracleBlock k) : OracleBlock k where
  labelCount := Fintype.card (WireLabel (twoBlocks B C) 2)
  start := controlLabel (twoBlocks B C) (0 : Fin 2)
  exit := controlLabel (twoBlocks B C) (1 : Fin 2)
  code := (wireMachine (twoBlocks B C) (loopControl stack B C) (fun _ => .inl 0) (.inl 0)).code
  exit_halt := wireMachine_control _ _ _ _ _

/-- An explicit finite loop execution records each actual pop and each actual
branch execution. A branch may alter any stack, including the tested stack. -/
inductive WhileExecution (stack : Fin (k+1)) (B C : OracleBlock k) (g : BitString → ℕ) :
    Store k → Store k → ℕ → Prop
  | empty (s) (h : s stack = []) : WhileExecution stack B C g s s 1
  | zero {s t u : Store k} {rest : BitString} {a b : ℕ}
      (h : s stack = false::rest)
      (body : B.Executes g (Function.update s stack rest) t a)
      (tail : WhileExecution stack B C g t u b) : WhileExecution stack B C g s u (1+a+1+b)
  | one {s t u : Store k} {rest : BitString} {a b : ℕ}
      (h : s stack = true::rest)
      (body : C.Executes g (Function.update s stack rest) t a)
      (tail : WhileExecution stack B C g t u b) : WhileExecution stack B C g s u (1+a+1+b)

/-- The structured loop semantics is proved to run in its actual finite machine. -/
theorem whilePop_executes (stack : Fin (k+1)) (B C : OracleBlock k) (g : BitString → ℕ)
    {s t : Store k} {cost : ℕ} (h : WhileExecution stack B C g s t cost) :
    (whilePop stack B C).Executes g s t cost := by
  let W := wireMachine (twoBlocks B C) (loopControl stack B C) (fun _ => .inl 0) (.inl 0)
  induction h with
  | empty s hs =>
    apply OracleMachine.Steps.single
    change W.step g ⟨controlLabel (twoBlocks B C) 0,s⟩ =
      some (⟨controlLabel (twoBlocks B C) 1,s⟩,1)
    simp [W,OracleMachine.step,wireMachine_control,loopControl,hs]
  | @zero s t u rest a b hs hb ht ih =>
    have hp : W.step g ⟨controlLabel (twoBlocks B C) 0,s⟩ =
        some (⟨blockLabel (twoBlocks B C) 0 B.start,Function.update s stack rest⟩,1) := by
      simp [W,OracleMachine.step,wireMachine_control,loopControl,hs]
    have hbody := wireMachine_executes_continuation (twoBlocks B C) (loopControl stack B C)
      (fun _ => .inl 0) (.inl 0) 0 g hb
    have hr := (OracleMachine.Steps.single hp).trans (hbody.trans ih)
    convert hr using 1 <;> omega
  | @one s t u rest a b hs hb ht ih =>
    have hp : W.step g ⟨controlLabel (twoBlocks B C) 0,s⟩ =
        some (⟨blockLabel (twoBlocks B C) 1 C.start,Function.update s stack rest⟩,1) := by
      simp [W,OracleMachine.step,wireMachine_control,loopControl,hs]
    have hbody := wireMachine_executes_continuation (twoBlocks B C) (loopControl stack B C)
      (fun _ => .inl 0) (.inl 0) 1 g hb
    have hr := (OracleMachine.Steps.single hp).trans (hbody.trans ih)
    convert hr using 1 <;> omega

/-- The two-label do-nothing block has a counted jump. -/
def skip : OracleBlock k where
  labelCount := 2
  start := 0
  exit := 1
  code q := if q = 0 then .jump 1 else .halt
  exit_halt := rfl

theorem skip_executes (g : BitString → ℕ) (s : Store k) : (skip (k := k)).Executes g s s 1 :=
  OracleMachine.Steps.single rfl

def push (stack : Fin (k+1)) (bit : Bool) : OracleBlock k where
  labelCount := 2
  start := 0
  exit := 1
  code q := if q = 0 then .push stack bit 1 else .halt
  exit_halt := rfl

theorem push_executes (g : BitString → ℕ) (stack : Fin (k+1)) (bit : Bool) (s : Store k) :
    (push stack bit).Executes g s (Function.update s stack (bit::s stack)) 1 :=
  OracleMachine.Steps.single rfl

def query (input output : Fin (k+1)) : OracleBlock k where
  labelCount := 2
  start := 0
  exit := 1
  code q := if q = 0 then .query input output 1 else .halt
  exit_halt := rfl

theorem query_executes (g : BitString → ℕ) (input output : Fin (k+1)) (s : Store k) :
    (query input output).Executes g s (Function.update s output (OracleMachine.answerBits g (s input)))
      (1+(s input).length+(OracleMachine.answerBits g (s input)).length) :=
  OracleMachine.Steps.single rfl

def threeBlocks (E B C : OracleBlock k) : Fin 3 → OracleBlock k :=
  Fin.cases E (Fin.cases B (fun _ => C))

noncomputable def branchControl (stack : Fin (k+1)) (E B C : OracleBlock k) :
    Fin 2 → OracleInstr (k+1) (Fintype.card (WireLabel (threeBlocks E B C) 2)) :=
  Fin.cases (.pop stack (blockLabel (threeBlocks E B C) 0 E.start)
    (blockLabel (threeBlocks E B C) 1 B.start) (blockLabel (threeBlocks E B C) 2 C.start)) (fun _ => .halt)

/-- Inspect and remove one bit, selecting the empty, false, or true branch. -/
noncomputable def branchPop (stack : Fin (k+1)) (E B C : OracleBlock k) : OracleBlock k where
  labelCount := Fintype.card (WireLabel (threeBlocks E B C) 2)
  start := controlLabel (threeBlocks E B C) (0 : Fin 2)
  exit := controlLabel (threeBlocks E B C) (1 : Fin 2)
  code := (wireMachine (threeBlocks E B C) (branchControl stack E B C) (fun _ => .inl 1) (.inl 0)).code
  exit_halt := wireMachine_control _ _ _ _ _

theorem branchPop_empty (stack : Fin (k+1)) (E B C : OracleBlock k) (g : BitString → ℕ)
    {s t : Store k} {cost : ℕ} (hs : s stack = []) (h : E.Executes g s t cost) :
    (branchPop stack E B C).Executes g s t (cost+2) := by
  let W := wireMachine (threeBlocks E B C) (branchControl stack E B C) (fun _ => .inl 1) (.inl 0)
  have hp : W.step g ⟨controlLabel (threeBlocks E B C) 0,s⟩ =
      some (⟨blockLabel (threeBlocks E B C) 0 E.start,s⟩,1) := by
    simp [W,OracleMachine.step,wireMachine_control,branchControl,hs]
  have hb := wireMachine_executes_continuation (threeBlocks E B C) (branchControl stack E B C)
    (fun _ => .inl 1) (.inl 0) 0 g h
  convert (OracleMachine.Steps.single hp).trans hb using 1 <;> omega

theorem branchPop_false (stack : Fin (k+1)) (E B C : OracleBlock k) (g : BitString → ℕ)
    {s t : Store k} {rest : BitString} {cost : ℕ} (hs : s stack = false::rest)
    (h : B.Executes g (Function.update s stack rest) t cost) :
    (branchPop stack E B C).Executes g s t (cost+2) := by
  let W := wireMachine (threeBlocks E B C) (branchControl stack E B C) (fun _ => .inl 1) (.inl 0)
  have hp : W.step g ⟨controlLabel (threeBlocks E B C) 0,s⟩ =
      some (⟨blockLabel (threeBlocks E B C) 1 B.start,Function.update s stack rest⟩,1) := by
    simp [W,OracleMachine.step,wireMachine_control,branchControl,hs]
  have hb := wireMachine_executes_continuation (threeBlocks E B C) (branchControl stack E B C)
    (fun _ => .inl 1) (.inl 0) 1 g h
  convert (OracleMachine.Steps.single hp).trans hb using 1 <;> omega

theorem branchPop_true (stack : Fin (k+1)) (E B C : OracleBlock k) (g : BitString → ℕ)
    {s t : Store k} {rest : BitString} {cost : ℕ} (hs : s stack = true::rest)
    (h : C.Executes g (Function.update s stack rest) t cost) :
    (branchPop stack E B C).Executes g s t (cost+2) := by
  let W := wireMachine (threeBlocks E B C) (branchControl stack E B C) (fun _ => .inl 1) (.inl 0)
  have hp : W.step g ⟨controlLabel (threeBlocks E B C) 0,s⟩ =
      some (⟨blockLabel (threeBlocks E B C) 2 C.start,Function.update s stack rest⟩,1) := by
    simp [W,OracleMachine.step,wireMachine_control,branchControl,hs]
  have hb := wireMachine_executes_continuation (threeBlocks E B C) (branchControl stack E B C)
    (fun _ => .inl 1) (.inl 0) 2 g h
  convert (OracleMachine.Steps.single hp).trans hb using 1 <;> omega

end HiddenCircuits.Complexity.OracleBlock
