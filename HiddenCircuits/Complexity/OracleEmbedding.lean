import HiddenCircuits.Complexity.OracleExecution

/-! Embed verified finite bit-program blocks into larger programs. The theorem
preserves each real instruction and exact oracle charge; halt labels may be
replaced by continuations because execution prefixes stop before them. -/
namespace HiddenCircuits.Complexity

namespace OracleInstr
def map {k q k' q' : ℕ} (stackMap : Fin k → Fin k') (labelMap : Fin q → Fin q') : OracleInstr k q → OracleInstr k' q'
  | .halt => .halt
  | .jump next => .jump (labelMap next)
  | .push i b next => .push (stackMap i) b (labelMap next)
  | .pop i empty zero one => .pop (stackMap i) (labelMap empty) (labelMap zero) (labelMap one)
  | .query i o next => .query (stackMap i) (stackMap o) (labelMap next)
end OracleInstr

namespace OracleMachine
variable (M N : OracleMachine)

def Corresponds (φ : Fin M.stackCount ↪ Fin N.stackCount) (ψ : Fin M.labelCount → Fin N.labelCount)
    (c : M.Config) (d : N.Config) : Prop :=
  d.pc = ψ c.pc ∧ ∀ i, d.stack (φ i) = c.stack i

/-- Structural instruction inclusion; it does not assert running time or a
problem-level reduction. Halt states can be used as block exits. -/
def EmbedsCode (φ : Fin M.stackCount ↪ Fin N.stackCount) (ψ : Fin M.labelCount → Fin N.labelCount) : Prop :=
  ∀ q, M.code q ≠ .halt → N.code (ψ q) = OracleInstr.map φ ψ (M.code q)

theorem step_embed (φ : Fin M.stackCount ↪ Fin N.stackCount) (ψ : Fin M.labelCount → Fin N.labelCount)
    (hcode : EmbedsCode M N φ ψ) (g : BitString → ℕ)
    {c c' : M.Config} {d : N.Config} {a : ℕ}
    (hc : Corresponds M N φ ψ c d) (hstep : M.step g c = some (c',a)) :
    ∃ d' : N.Config, N.step g d = some (d',a) ∧ Corresponds M N φ ψ c' d' := by
  obtain ⟨hpc,hs⟩ := hc
  cases hi : M.code c.pc with
  | halt => simp [step,hi] at hstep
  | jump next =>
    have hn := hcode c.pc (by simp [hi])
    simp only [hi,OracleInstr.map] at hn
    simp only [step,hi] at hstep
    cases hstep
    refine ⟨⟨ψ next,d.stack⟩,?_,rfl,hs⟩
    simp [step,hpc,hn]
  | push i b next =>
    have hn := hcode c.pc (by simp [hi])
    simp only [hi,OracleInstr.map] at hn
    simp only [step,hi] at hstep
    cases hstep
    refine ⟨⟨ψ next,Function.update d.stack (φ i) (b::d.stack (φ i))⟩,?_,rfl,?_⟩
    · simp [step,hpc,hn]
    · intro j
      simp [Function.update_apply,φ.injective.eq_iff,hs]
  | pop i empty zero one =>
    have hn := hcode c.pc (by simp [hi])
    simp only [hi,OracleInstr.map] at hn
    cases he : c.stack i with
    | nil =>
      simp only [step,hi,he] at hstep
      cases hstep
      refine ⟨⟨ψ empty,d.stack⟩,?_,rfl,hs⟩
      simp [step,hpc,hn,hs,he]
    | cons b bs =>
      simp only [step,hi,he] at hstep
      cases hstep
      refine ⟨⟨ψ (if b then one else zero),Function.update d.stack (φ i) bs⟩,?_,rfl,?_⟩
      · cases b <;> simp [step,hpc,hn,hs,he]
      · intro j
        simp [Function.update_apply,φ.injective.eq_iff,hs]
  | query i o next =>
    have hn := hcode c.pc (by simp [hi])
    simp only [hi,OracleInstr.map] at hn
    simp only [step,hi] at hstep
    cases hstep
    refine ⟨⟨ψ next,Function.update d.stack (φ o) (answerBits g (c.stack i))⟩,?_,rfl,?_⟩
    · simp [step,hpc,hn,hs]
    · intro j
      simp [Function.update_apply,φ.injective.eq_iff,hs]

/-- Exact prefix-cost preservation under verified block embedding. -/
theorem steps_embed (φ : Fin M.stackCount ↪ Fin N.stackCount) (ψ : Fin M.labelCount → Fin N.labelCount)
    (hcode : EmbedsCode M N φ ψ) (g : BitString → ℕ)
    {c c' : M.Config} {d : N.Config} {t : ℕ}
    (hc : Corresponds M N φ ψ c d) (h : M.Steps g c c' t) :
    ∃ d' : N.Config, N.Steps g d d' t ∧ Corresponds M N φ ψ c' d' := by
  induction h generalizing d with
  | refl c => exact ⟨d,Steps.refl d,hc⟩
  | next hs tail ih =>
    obtain ⟨d₁,hd₁,hc₁⟩ := step_embed M N φ ψ hcode g hc hs
    obtain ⟨d₂,hd₂,hc₂⟩ := ih hc₁
    exact ⟨d₂,Steps.next hd₁ hd₂,hc₂⟩

/-- A mapped instruction leaves every non-block stack unchanged. -/
theorem mapped_step_frame (φ : Fin M.stackCount ↪ Fin N.stackCount)
    (ψ : Fin M.labelCount → Fin N.labelCount) (instr : OracleInstr M.stackCount M.labelCount)
    (g : BitString → ℕ) {c d : N.Config} {a : ℕ}
    (hcode : N.code c.pc = OracleInstr.map φ ψ instr) (hs : N.step g c = some (d,a))
    (j : Fin N.stackCount) (hj : ∀ i, φ i ≠ j) : d.stack j = c.stack j := by
  cases instr with
  | halt => simp [step,hcode,OracleInstr.map] at hs
  | jump next => simp only [step,hcode,OracleInstr.map] at hs; cases hs; rfl
  | push i b next =>
    simp only [step,hcode,OracleInstr.map] at hs
    cases hs
    exact Function.update_of_ne (hj i).symm _ _
  | pop i empty zero one =>
    simp only [step,hcode,OracleInstr.map] at hs
    split at hs
    · cases hs; rfl
    · cases hs; exact Function.update_of_ne (hj i).symm _ _
  | query i o next =>
    simp only [step,hcode,OracleInstr.map] at hs
    cases hs
    exact Function.update_of_ne (hj o).symm _ _

/-- Block embedding with its complete frame property and exact charged cost. -/
theorem steps_embed_frame (φ : Fin M.stackCount ↪ Fin N.stackCount)
    (ψ : Fin M.labelCount → Fin N.labelCount) (hcode : EmbedsCode M N φ ψ) (g : BitString → ℕ)
    {c c' : M.Config} {d : N.Config} {t : ℕ}
    (hc : Corresponds M N φ ψ c d) (h : M.Steps g c c' t) :
    ∃ d' : N.Config, N.Steps g d d' t ∧ Corresponds M N φ ψ c' d' ∧
      ∀ j, (∀ i, φ i ≠ j) → d'.stack j = d.stack j := by
  induction h generalizing d with
  | refl c => exact ⟨d,Steps.refl d,hc,fun _ _ => rfl⟩
  | @next c₀ c₁ c₂ a b hs tail ih =>
    obtain ⟨d₁,hd₁,hc₁⟩ := step_embed M N φ ψ hcode g hc hs
    have hn : M.code c₀.pc ≠ .halt := by intro he; simp [step,he] at hs
    have hcCode : N.code d.pc = OracleInstr.map φ ψ (M.code c₀.pc) := by rw [hc.1,hcode _ hn]
    have hframe₁ := mapped_step_frame M N φ ψ (M.code c₀.pc) g hcCode hd₁
    obtain ⟨d₂,hd₂,hc₂,hframe₂⟩ := ih hc₁
    refine ⟨d₂,Steps.next hd₁ hd₂,hc₂,?_⟩
    exact fun j hj => (hframe₂ j hj).trans (hframe₁ j hj)

end OracleMachine
end HiddenCircuits.Complexity
