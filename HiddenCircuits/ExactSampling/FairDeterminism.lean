import HiddenCircuits.ExactSampling.FairCode

/-! Determinism of charged fair-coin execution, including variable-length bit
consumption. A fixed stream cannot have two distinct terminating prefixes. -/
namespace HiddenCircuits.ExactSampling
open Complexity OracleBlock

 theorem oracle_runs_unique (M : OracleMachine) {s t u : M.Config} {a b : ℕ}
    (h : M.Runs (fun _=>0) s t a) (h' : M.Runs (fun _=>0) s u b) : t=u ∧ a=b := by
  induction h generalizing u b with
  | halt s hs =>
    cases h' with
    | halt _ _ => exact ⟨rfl,rfl⟩
    | next he ht => rw [hs] at he;contradiction
  | @next s t v a b he ht ih =>
    cases h' with
    | halt _ hs => rw [hs] at he;contradiction
    | @next _ t' v' a' b' he' ht' =>
      have hh := Option.some.inj (he.symm.trans he')
      cases hh
      obtain ⟨rfl,rfl⟩ := ih ht'
      exact ⟨rfl,rfl⟩

 theorem block_executes_unique {k : ℕ} (B : OracleBlock k) {s t u : Store k} {a b : ℕ}
    (h : B.Executes (fun _=>0) s t a) (h' : B.Executes (fun _=>0) s u b) : t=u ∧a=b := by
  have ht : B.machine.Runs (fun _=>0) (B.config B.start s) (B.config B.exit t) a :=
    (OracleMachine.runs_iff_steps_halt _).mpr ⟨h,by simp [OracleMachine.step,machine,config,B.exit_halt]⟩
  have hu : B.machine.Runs (fun _=>0) (B.config B.start s) (B.config B.exit u) b :=
    (OracleMachine.runs_iff_steps_halt _).mpr ⟨h',by simp [OracleMachine.step,machine,config,B.exit_halt]⟩
  obtain ⟨he,hc⟩ := oracle_runs_unique B.machine ht hu
  exact ⟨congrArg (fun c => c.stack) he,hc⟩

namespace FairCode
variable {k : ℕ}

/-- If two terminating executions receive compatible prefixes of one stream,
they consume precisely the same prefix and have the same output and charge. -/
 theorem Runs.deterministic {P : FairCode k} {s t : Store k} {xs : List Bool} {c : ℕ}
    (h : Runs P s t xs c) :
    ∀ {u : Store k} {ys : List Bool} {d : ℕ},Runs P s u ys d→
      ∀left right : List Bool,xs++left=ys++right→t=u ∧xs=ys ∧left=right ∧c=d := by
  induction h with
  | block hb =>
    intro u ys d h' left right he
    cases h' with
    | block hb' =>
      obtain ⟨rfl,rfl⟩ := block_executes_unique _ hb hb'
      exact ⟨rfl,rfl,he,rfl⟩
  | coin s stack b =>
    intro u ys d h' left right he
    cases h' with
    | coin _ _ b' =>
      obtain ⟨hbit,htail⟩ := List.cons.inj he
      subst b'
      exact ⟨rfl,rfl,htail,rfl⟩
  | @seq B C s t u xs ys a b hB hC ihB ihC =>
    intro v zs d h' left right he
    cases h' with
    | @seq _ _ _ t' _ xs' ys' a' b' hB' hC' =>
      have he' : xs++(ys++left)=xs'++(ys'++right) := by simpa only [List.append_assoc] using he
      obtain ⟨ht,hxs,htail,ha⟩ := ihB hB' (ys++left) (ys'++right) he'
      subst t';subst xs';subst a'
      obtain ⟨hu,hys,hl,hb⟩ := ihC hC' left right htail
      subst v;subst ys';subst b'
      exact ⟨rfl,rfl,hl,rfl⟩
  | branchEmpty hs hr ih =>
    intro u ys d h' left right he
    cases h' with
    | branchEmpty _ hr' =>
      obtain ⟨ht,hx,hl,hc⟩ := ih hr' left right he
      exact ⟨ht,hx,hl,by omega⟩
    | branchFalse hs' _ => rw [hs] at hs';contradiction
    | branchTrue hs' _ => rw [hs] at hs';contradiction
  | @branchFalse q E B C s t rest xs c hs hr ih =>
    intro u ys d h' left right he
    cases h' with
    | branchEmpty hs' _ => rw [hs'] at hs;contradiction
    | @branchFalse _ _ _ _ _ _ rest' _ _ hs' hr' =>
      have heq := List.cons.inj (hs.symm.trans hs')
      cases heq.2
      obtain ⟨ht,hx,hl,hc⟩ := ih hr' left right he
      exact ⟨ht,hx,hl,by omega⟩
    | branchTrue hs' _ => have hh:=List.cons.inj (hs.symm.trans hs');cases hh.1
  | @branchTrue q E B C s t rest xs c hs hr ih =>
    intro u ys d h' left right he
    cases h' with
    | branchEmpty hs' _ => rw [hs'] at hs;contradiction
    | branchFalse hs' _ => have hh:=List.cons.inj (hs.symm.trans hs');cases hh.1
    | @branchTrue _ _ _ _ _ _ rest' _ _ hs' hr' =>
      have heq := List.cons.inj (hs.symm.trans hs')
      cases heq.2
      obtain ⟨ht,hx,hl,hc⟩ := ih hr' left right he
      exact ⟨ht,hx,hl,by omega⟩
  | loopEmpty s hs =>
    intro u ys d h' left right he
    cases h' with
    | loopEmpty _ _ => exact ⟨rfl,rfl,he,rfl⟩
    | loopFalse hs' _ _ => rw [hs] at hs';contradiction
    | loopTrue hs' _ _ => rw [hs] at hs';contradiction
  | @loopFalse q B C s t u rest xs ys a b hs hB hC ihB ihC =>
    intro v zs d h' left right he
    cases h' with
    | loopEmpty _ hs' => rw [hs'] at hs;contradiction
    | loopTrue hs' _ _ => have hh:=List.cons.inj (hs.symm.trans hs');cases hh.1
    | @loopFalse _ _ _ _ t' _ rest' xs' ys' a' b' hs' hB' hC' =>
      have heq := List.cons.inj (hs.symm.trans hs')
      cases heq.2
      have he' : xs++(ys++left)=xs'++(ys'++right) := by simpa only [List.append_assoc] using he
      obtain ⟨ht,hxs,htail,ha⟩ := ihB hB' (ys++left) (ys'++right) he'
      subst t';subst xs';subst a'
      obtain ⟨hu,hys,hl,hb⟩ := ihC hC' left right htail
      subst v;subst ys';subst b'
      exact ⟨rfl,rfl,hl,rfl⟩
  | @loopTrue q B C s t u rest xs ys a b hs hB hC ihB ihC =>
    intro v zs d h' left right he
    cases h' with
    | loopEmpty _ hs' => rw [hs'] at hs;contradiction
    | loopFalse hs' _ _ => have hh:=List.cons.inj (hs.symm.trans hs');cases hh.1
    | @loopTrue _ _ _ _ t' _ rest' xs' ys' a' b' hs' hB' hC' =>
      have heq := List.cons.inj (hs.symm.trans hs')
      cases heq.2
      have he' : xs++(ys++left)=xs'++(ys'++right) := by simpa only [List.append_assoc] using he
      obtain ⟨ht,hxs,htail,ha⟩ := ihB hB' (ys++left) (ys'++right) he'
      subst t';subst xs';subst a'
      obtain ⟨hu,hys,hl,hb⟩ := ihC hC' left right htail
      subst v;subst ys';subst b'
      exact ⟨rfl,rfl,hl,rfl⟩

 theorem Runs.cost_unique {P : FairCode k} {s t u : Store k} {xs : List Bool} {a b : ℕ}
    (h : Runs P s t xs a) (h' : Runs P s u xs b) : a=b :=
  (h.deterministic h' [] [] rfl).2.2.2

end FairCode
end HiddenCircuits.ExactSampling
