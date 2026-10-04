import HiddenCircuits.Complexity.TM2Tableau

/-! Concrete stack-space bounds for mathlib's finite TM2 verifier. A macrostep
cannot hide unbounded stack growth: its finite syntax supplies a fixed budget. -/
namespace HiddenCircuits.Complexity
namespace TM2Space

open Turing.TM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- Maximum pushes along a branch of one finite statement. -/
def pushBudget : Stmt Γ Λ σ → ℕ
  | .push _ _ s => pushBudget s + 1
  | .peek _ _ s => pushBudget s
  | .pop _ _ s => pushBudget s
  | .load _ s => pushBudget s
  | .branch _ s t => max (pushBudget s) (pushBudget t)
  | .goto _ => 0
  | .halt => 0

variable [DecidableEq K]

theorem stepAux_stack_bound (s : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (n : ℕ)
    (hS : ∀ k, (S k).length ≤ n) :
    ∀ k, ((stepAux s v S).stk k).length ≤ n + pushBudget s := by
  induction s generalizing v S n with
  | push i f s ih =>
    have hnew : ∀ k, (Function.update S i (f v :: S i) k).length ≤ n+1 := by
      intro k
      by_cases hk : k = i
      · subst k; simpa using Nat.add_le_add_right (hS i) 1
      · simpa [Function.update_of_ne hk] using (hS k).trans (Nat.le_add_right n 1)
    simpa [stepAux,pushBudget,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih v _ (n+1) hnew
  | peek i f s ih => exact ih _ S n hS
  | pop i f s ih =>
    have hnew : ∀ k, (Function.update S i (S i).tail k).length ≤ n := by
      intro k
      by_cases hk : k = i
      · subst k
        simp only [Function.update_self]
        have hi := hS i
        simp only [List.length_tail]
        omega
      · simpa [Function.update_of_ne hk] using hS k
    exact ih _ _ n hnew
  | load f s ih => exact ih _ S n hS
  | branch f s t ihs iht =>
    intro k
    cases hf : f v with
    | false =>
      simpa [stepAux,hf,pushBudget] using
        (iht v S n hS k).trans (Nat.add_le_add_left (Nat.le_max_right _ _) n)
    | true =>
      simpa [stepAux,hf,pushBudget] using
        (ihs v S n hS k).trans (Nat.add_le_add_left (Nat.le_max_left _ _) n)
  | goto f => simpa [stepAux,pushBudget] using hS
  | halt => simpa [stepAux,pushBudget] using hS

/-- A machine-dependent constant, computed from every finite control statement. -/
def machineBudget (M : Turing.FinTM2) : ℕ := by
  letI := M.ΛFin
  exact ∑ l : M.Λ, pushBudget (M.m l)

theorem statement_le_machineBudget (M : Turing.FinTM2) (l : M.Λ) :
    pushBudget (M.m l) ≤ machineBudget M := by
  letI := M.ΛFin
  change pushBudget (M.m l) ≤ ∑ l : M.Λ, pushBudget (M.m l)
  exact Finset.single_le_sum (f := fun l : M.Λ => pushBudget (M.m l)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

/-- One actual macrostep has the proved constant stack-growth bound. -/
theorem step_stack_bound (M : Turing.FinTM2) (c d : M.Cfg) (n : ℕ)
    (h : M.step c = some d) (hc : ∀ k, (c.stk k).length ≤ n) :
    ∀ k, (d.stk k).length ≤ n + machineBudget M := by
  rcases c with ⟨label,v,S⟩
  cases label with
  | none => contradiction
  | some l =>
    have hd : d = stepAux (M.m l) v S := by exact (Option.some.inj h).symm
    subst d
    intro k
    exact (stepAux_stack_bound (M.m l) v S n hc k).trans
      (Nat.add_le_add_left (statement_le_machineBudget M l) n)

/-- Stuttering after halting does not increase the stack bound. -/
theorem stutter_stack_bound (M : Turing.FinTM2) (c : M.Cfg) (n : ℕ)
    (hc : ∀ k, (c.stk k).length ≤ n) :
    ∀ k, ((stutter M.step c).stk k).length ≤ n + machineBudget M := by
  cases h : M.step c with
  | none =>
    rw [stutter_halt h]
    exact fun k => (hc k).trans (Nat.le_add_right _ _)
  | some d =>
    unfold stutter
    rw [h]
    exact step_stack_bound M c d n h hc

/-- Every stack in a `t`-step tableau has linear height in input size and time. -/
theorem iterate_stack_bound (M : Turing.FinTM2) (c : M.Cfg) (n t : ℕ)
    (hc : ∀ k, (c.stk k).length ≤ n) :
    ∀ k, (((stutter M.step)^[t] c).stk k).length ≤ n + t*machineBudget M := by
  induction t with
  | zero => simpa using hc
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simpa [Nat.succ_mul,Nat.add_assoc] using stutter_stack_bound M _ _ ih

lemma initial_stack_bound (M : Turing.FinTM2) (x : List (M.Γ M.k₀)) :
    ∀ k, ((Turing.initList M x).stk k).length ≤ x.length := by
  intro k
  unfold Turing.initList
  dsimp only
  split_ifs with h
  · subst k; exact le_rfl
  · exact Nat.zero_le _

/-- Actual finite TM2 configurations in the canonical input tableau have bounded
stack heights; this is not a promised-space assumption. -/
theorem input_tableau_stack_bound (M : Turing.FinTM2) (x : List (M.Γ M.k₀)) (t : ℕ) :
    ∀ k, (((stutter M.step)^[t] (Turing.initList M x)).stk k).length ≤
      x.length+t*machineBudget M :=
  iterate_stack_bound M _ _ _ (initial_stack_bound M x)

end TM2Space
end HiddenCircuits.Complexity
