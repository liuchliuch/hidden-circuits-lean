import HiddenCircuits.Complexity.OracleBitPrograms

/-! Actual instruction-level simulation of oracle-free binary-stack programs by
mathlib's finite TM2. One bit instruction becomes one bounded TM2 macrostep;
the terminal halt resets the finite register in one further step. -/
namespace HiddenCircuits.Complexity
namespace OracleMachine

/-- Syntactic absence of oracle instructions. -/
def QueryFree (M : OracleMachine) : Prop :=
  ∀ q i o next, M.code q ≠ .query i o next

open Turing.TM2

def binaryStmt {k q : ℕ} : OracleInstr k q → Stmt (fun _ : Fin k => Bool) (Fin q) (Option Bool)
  | .halt => .load (fun _ => none) .halt
  | .jump next => .goto (fun _ => next)
  | .push i bit next => .push i (fun _ => bit) (.goto (fun _ => next))
  | .pop i empty zero one => .pop i (fun _ b => b)
      (.goto (fun b => match b with | none => empty | some false => zero | some true => one))
  | .query _ _ _ => .halt

/-- A concrete mathlib finite TM2, with precisely the same Boolean stacks and
finite labels as the source program. -/
def binaryTM2 (M : OracleMachine) : Turing.FinTM2 where
  K := Fin M.stackCount
  k₀ := M.input
  k₁ := M.output
  Γ _ := Bool
  Λ := Fin M.labelCount
  main := M.start
  σ := Option Bool
  initialState := none
  m q := binaryStmt (M.code q)

def binaryConfig (M : OracleMachine) (c : M.Config) (v : Option Bool) : M.binaryTM2.Cfg :=
  ⟨some c.pc,v,c.stack⟩

def binaryHalt (M : OracleMachine) (s : Fin M.stackCount → BitString) : M.binaryTM2.Cfg :=
  ⟨none,none,s⟩

@[ext] theorem tm2Cfg_ext {K : Type} {Γ : K → Type} {Λ σ : Type}
    {a b : Cfg Γ Λ σ} (hl : a.l = b.l) (hv : a.var = b.var) (hs : a.stk = b.stk) : a = b := by
  cases a;cases b;simp_all

/-- The translation preserves the complete stack store after every real step. -/
theorem binary_step (M : OracleMachine) (hq : M.QueryFree) (g : BitString → ℕ)
    {c d : M.Config} {cost : ℕ} (h : M.step g c = some (d,cost)) (v : Option Bool) :
    cost = 1 ∧ ∃ w : Option Bool, M.binaryTM2.step (M.binaryConfig c v) = some (M.binaryConfig d w) := by
  cases hi : M.code c.pc with
  | halt => simp [step,hi] at h
  | jump next =>
    simp only [step,hi] at h
    cases h
    refine ⟨rfl,v,?_⟩
    change some (stepAux (binaryStmt (M.code c.pc)) v c.stack) = _
    rw [hi]
    rfl
  | push i bit next =>
    simp only [step,hi] at h
    cases h
    refine ⟨rfl,v,?_⟩
    change some (stepAux (binaryStmt (M.code c.pc)) v c.stack) = _
    rw [hi]
    rfl
  | pop i empty zero one =>
    cases hs : c.stack i with
    | nil =>
      simp only [step,hi,hs] at h
      cases h
      refine ⟨rfl,none,?_⟩
      change some (stepAux (binaryStmt (M.code c.pc)) v c.stack) = _
      rw [hi]
      simp only [binaryStmt,stepAux,hs,List.head?_nil,List.tail_nil]
      congr 1
      apply tm2Cfg_ext
      · rfl
      · rfl
      · exact Function.update_eq_self_iff.mpr hs.symm
    | cons bit bs =>
      simp only [step,hi,hs] at h
      cases h
      refine ⟨rfl,some bit,?_⟩
      change some (stepAux (binaryStmt (M.code c.pc)) v c.stack) = _
      rw [hi]
      cases bit <;> simp [binaryStmt,stepAux,hs,binaryConfig]
  | query i o next => exact False.elim (hq c.pc i o next hi)

lemma binary_halt_step (M : OracleMachine) (g : BitString → ℕ) {c : M.Config}
    (h : M.step g c = none) (v : Option Bool) :
    M.binaryTM2.step (M.binaryConfig c v) = some (M.binaryHalt c.stack) := by
  have hc : M.code c.pc = .halt := by
    cases hi : M.code c.pc <;> simp [step,hi] at h ⊢
    split at h <;> contradiction
  change some (stepAux (binaryStmt (M.code c.pc)) v c.stack) = _
  rw [hc]
  rfl

private def oneStep {α : Type} {f : α → Option α} {a b : α} (h : f a = some b) :
    StateTransition.EvalsToInTime f a (some b) 1 :=
  ⟨⟨1,h⟩,le_rfl⟩

/-- Full terminating execution is simulated with exactly one extra macrostep.
All auxiliary stacks are still represented, rather than silently discarded. -/
theorem binary_runs (M : OracleMachine) (hq : M.QueryFree) (g : BitString → ℕ)
    {c d : M.Config} {cost : ℕ} (h : M.Runs g c d cost) (v : Option Bool) :
    Nonempty (StateTransition.EvalsToInTime M.binaryTM2.step
      (M.binaryConfig c v) (some (M.binaryHalt d.stack)) (cost+1)) := by
  induction h generalizing v with
  | halt c h => exact ⟨oneStep (binary_halt_step M g h v)⟩
  | @next c d e a b hs tail ih =>
    obtain ⟨ha,w,hw⟩ := binary_step M hq g hs v
    subst a
    obtain ⟨ht⟩ := ih w
    have hr := StateTransition.EvalsToInTime.trans M.binaryTM2.step 1 (b+1)
      (M.binaryConfig c v) (M.binaryConfig d w) (some (M.binaryHalt e.stack)) (oneStep hw) ht
    exact ⟨by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hr⟩

lemma binary_init (M : OracleMachine) (x : BitString) :
    Turing.initList M.binaryTM2 x = M.binaryConfig (M.init x) none := by
  apply tm2Cfg_ext
  · rfl
  · rfl
  · funext i
    simp [Turing.initList,binaryTM2,binaryConfig,init,Function.update_apply]

lemma binary_haltList (M : OracleMachine) (c : M.Config)
    (hc : ∀ i, i ≠ M.output → c.stack i = []) :
    M.binaryHalt c.stack = Turing.haltList M.binaryTM2 (c.stack M.output) := by
  apply tm2Cfg_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i = M.output
    · subst i;simp [binaryHalt,Turing.haltList,binaryTM2]
    · simp [binaryHalt,Turing.haltList,binaryTM2,hi,hc i hi]

/-- A clean polynomial-time binary program gives genuine mathlib TM2
polynomial-time computability. The hypotheses are its real execution theorem
and full final-store invariant, not an assumed complexity flag. -/
noncomputable def computableOfBinary {f : BitString → BitString} (M : OracleMachine)
    (hq : M.QueryFree) (p : Polynomial ℕ)
    (h : ∀ x, ∃ c : M.Config, ∃ cost : ℕ, M.Runs (fun _ => 0) (M.init x) c cost ∧
      c.stack M.output = f x ∧ (∀ i, i ≠ M.output → c.stack i = []) ∧ cost ≤ p.eval x.length) :
    Turing.TM2ComputableInPolyTime id id f where
  tm := M.binaryTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := p+1
  outputsFun x := by
    apply Classical.choice
    obtain ⟨c,cost,hr,ho,hclean,hcost⟩ := h x
    obtain ⟨ht⟩ := binary_runs M hq (fun _ => 0) hr none
    rw [← binary_init,binary_haltList M c hclean,ho] at ht
    refine ⟨{ steps := ht.steps, evals_in_steps := ?_, steps_le_m := ?_ }⟩
    · simpa [Equiv.refl] using ht.evals_in_steps
    · exact ht.steps_le_m.trans (by simpa using Nat.add_le_add_right hcost 1)

theorem polyTime_of_binary {f : BitString → BitString} (M : OracleMachine)
    (hq : M.QueryFree) (p : Polynomial ℕ)
    (h : ∀ x, ∃ c : M.Config, ∃ cost : ℕ, M.Runs (fun _ => 0) (M.init x) c cost ∧
      c.stack M.output = f x ∧ (∀ i, i ≠ M.output → c.stack i = []) ∧ cost ≤ p.eval x.length) :
    PolyTime f := ⟨computableOfBinary M hq p h⟩

end OracleMachine
end HiddenCircuits.Complexity
