import HiddenCircuits.Complexity.OracleEmbedding
import HiddenCircuits.Complexity.OracleBitPrograms

/-! Finite block wiring. Every component is actual bit-instruction code.
Connecting a block to its continuation costs one actual jump instruction.
The finite label enumeration depends only on the fixed program, never on input. -/
namespace HiddenCircuits.Complexity

/-- A finite bit-program fragment with one designated exit. Other halts are
permitted, but cannot occur in a proved prefix reaching the designated exit. -/
structure OracleBlock (k : ℕ) where
  labelCount : ℕ
  start : Fin labelCount
  exit : Fin labelCount
  code : Fin labelCount → OracleInstr (k+1) labelCount
  exit_halt : code exit = .halt

namespace OracleBlock
variable {k : ℕ}

def machine (B : OracleBlock k) : OracleMachine where
  stackCount := k+1
  labelCount := B.labelCount
  input := 0
  output := 0
  start := B.start
  code := B.code

abbrev Store (k : ℕ) := Fin (k+1) → BitString

def config (B : OracleBlock k) (q : Fin B.labelCount) (s : Store k) : B.machine.Config := ⟨q,s⟩

abbrev Executes (B : OracleBlock k) (g : BitString → ℕ) (s t : Store k) (cost : ℕ) : Prop :=
  B.machine.Steps g (B.config B.start s) (B.config B.exit t) cost

/-- Labels of a finite network of blocks and control instructions. -/
def WireLabel {b : ℕ} (blocks : Fin b → OracleBlock k) (c : ℕ) :=
  Fin c ⊕ ((i : Fin b) × Fin (blocks i).labelCount)

instance {b c : ℕ} (blocks : Fin b → OracleBlock k) : Fintype (WireLabel blocks c) :=
  inferInstanceAs (Fintype (Fin c ⊕ ((i : Fin b) × Fin (blocks i).labelCount)))

noncomputable def wireEquiv {b c : ℕ} (blocks : Fin b → OracleBlock k) :
    WireLabel blocks c ≃ Fin (Fintype.card (WireLabel blocks c)) := Fintype.equivFin _

noncomputable def blockLabel {b c : ℕ} (blocks : Fin b → OracleBlock k) (i : Fin b)
    (q : Fin (blocks i).labelCount) : Fin (Fintype.card (WireLabel blocks c)) :=
  wireEquiv blocks (.inr ⟨i,q⟩)

noncomputable def controlLabel {b c : ℕ} (blocks : Fin b → OracleBlock k) (q : Fin c) :
    Fin (Fintype.card (WireLabel blocks c)) := wireEquiv blocks (.inl q)

/-- Actual finite code after connecting each block exit to its specified
continuation. Control instructions themselves are ordinary bit instructions. -/
noncomputable def wireMachine {b c : ℕ} (blocks : Fin b → OracleBlock k)
    (control : Fin c → OracleInstr (k+1) (Fintype.card (WireLabel blocks c)))
    (continuation : Fin b → WireLabel blocks c) (start : WireLabel blocks c) : OracleMachine where
  stackCount := k+1
  labelCount := Fintype.card (WireLabel blocks c)
  input := 0
  output := 0
  start := wireEquiv blocks start
  code q := match (wireEquiv blocks).symm q with
    | .inl l => control l
    | .inr ⟨i,l⟩ => if l = (blocks i).exit then .jump (wireEquiv blocks (continuation i))
      else OracleInstr.map id (blockLabel blocks i) ((blocks i).code l)

@[simp] theorem wireMachine_control {b c : ℕ} (blocks : Fin b → OracleBlock k)
    (control : Fin c → OracleInstr (k+1) (Fintype.card (WireLabel blocks c)))
    (continuation : Fin b → WireLabel blocks c) (start : WireLabel blocks c) (q : Fin c) :
    (wireMachine blocks control continuation start).code (controlLabel blocks q) = control q := by
  simp [wireMachine,controlLabel]

@[simp] theorem wireMachine_block {b c : ℕ} (blocks : Fin b → OracleBlock k)
    (control : Fin c → OracleInstr (k+1) (Fintype.card (WireLabel blocks c)))
    (continuation : Fin b → WireLabel blocks c) (start : WireLabel blocks c)
    (i : Fin b) (q : Fin (blocks i).labelCount) :
    (wireMachine blocks control continuation start).code (blockLabel blocks i q) =
      if q = (blocks i).exit then .jump (wireEquiv blocks (continuation i))
      else OracleInstr.map id (blockLabel blocks i) ((blocks i).code q) := by
  simp [wireMachine,blockLabel]

/-- All actual non-halting instructions are embedded unchanged. -/
theorem wireMachine_embeds {b c : ℕ} (blocks : Fin b → OracleBlock k)
    (control : Fin c → OracleInstr (k+1) (Fintype.card (WireLabel blocks c)))
    (continuation : Fin b → WireLabel blocks c) (start : WireLabel blocks c) (i : Fin b) :
    OracleMachine.EmbedsCode (blocks i).machine (wireMachine blocks control continuation start)
      (Function.Embedding.refl _) (blockLabel blocks i) := by
  intro q h
  have hq : q ≠ (blocks i).exit := by
    intro he
    subst q
    exact h (blocks i).exit_halt
  simp only [wireMachine_block,if_neg hq]
  rfl

/-- Prefix correctness survives wiring, with exactly the same bit-operation
charge and every stack (including temporary stacks) accounted for. -/
theorem wireMachine_executes {b c : ℕ} (blocks : Fin b → OracleBlock k)
    (control : Fin c → OracleInstr (k+1) (Fintype.card (WireLabel blocks c)))
    (continuation : Fin b → WireLabel blocks c) (start : WireLabel blocks c) (i : Fin b)
    (g : BitString → ℕ) {s t : Store k} {cost : ℕ}
    (h : (blocks i).Executes g s t cost) :
    (wireMachine blocks control continuation start).Steps g
      ⟨blockLabel blocks i (blocks i).start,s⟩
      ⟨blockLabel blocks i (blocks i).exit,t⟩ cost := by
  let N := wireMachine blocks control continuation start
  obtain ⟨d,hd,hc⟩ := OracleMachine.steps_embed (blocks i).machine N
    (Function.Embedding.refl _) (blockLabel blocks i)
    (wireMachine_embeds blocks control continuation start i) g
    (d := ⟨blockLabel blocks i (blocks i).start,s⟩) ⟨rfl,fun _ => rfl⟩ h
  have he : d = ⟨blockLabel blocks i (blocks i).exit,t⟩ := by
    apply OracleConfig.ext hc.1
    exact hc.2
  rwa [he] at hd

/-- A wired block really executes its continuation jump; it does not smuggle
control flow into a cost-free semantic rule. -/
theorem wireMachine_executes_continuation {b c : ℕ} (blocks : Fin b → OracleBlock k)
    (control : Fin c → OracleInstr (k+1) (Fintype.card (WireLabel blocks c)))
    (continuation : Fin b → WireLabel blocks c) (start : WireLabel blocks c) (i : Fin b)
    (g : BitString → ℕ) {s t : Store k} {cost : ℕ}
    (h : (blocks i).Executes g s t cost) :
    (wireMachine blocks control continuation start).Steps g
      ⟨blockLabel blocks i (blocks i).start,s⟩
      ⟨wireEquiv blocks (continuation i),t⟩ (cost+1) := by
  apply (wireMachine_executes blocks control continuation start i g h).trans
  apply OracleMachine.Steps.single
  simp [OracleMachine.step,wireMachine_block]

end OracleBlock
end HiddenCircuits.Complexity
