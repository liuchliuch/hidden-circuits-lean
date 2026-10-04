import HiddenCircuits.Complexity.SharpP

/-!
# Unique deterministic computation tableaux

These lemmas establish the counting-sensitive uniqueness obligation before any
CNF encoding: adding the complete deterministic history introduces exactly one
extension per certificate, including at a fixed padded horizon.
-/
namespace HiddenCircuits.Complexity

/-- A complete bounded history of a deterministic transition function. -/
@[ext] structure Tableau {σ : Type*} (next : σ → σ) (initial : σ) (time : ℕ) where
  state : Fin (time+1) → σ
  at_zero : state 0 = initial
  transition : ∀ i : Fin time, state i.succ = next (state i.castSucc)

namespace Tableau
variable {σ : Type*} {next : σ → σ} {initial : σ} {time : ℕ}

def canonical (next : σ → σ) (initial : σ) (time : ℕ) : Tableau next initial time where
  state i := next^[i.val] initial
  at_zero := rfl
  transition i := Function.iterate_succ_apply' _ _ _

theorem state_eq_iterate (T : Tableau next initial time) (i : Fin (time+1)) :
    T.state i = next^[i.val] initial := by
  induction i using Fin.induction with
  | zero => exact T.at_zero
  | succ i ih =>
    rw [T.transition i, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

theorem eq_canonical (T : Tableau next initial time) : T = canonical next initial time := by
  apply Tableau.ext
  funext i
  exact T.state_eq_iterate i

instance : Subsingleton (Tableau next initial time) :=
  ⟨fun T U => T.eq_canonical.trans U.eq_canonical.symm⟩

instance : Unique (Tableau next initial time) :=
  ⟨⟨canonical next initial time⟩, fun _ => Subsingleton.elim _ _⟩

@[simp] theorem final_state (T : Tableau next initial time) :
    T.state (Fin.last time) = next^[time] initial := T.state_eq_iterate _

end Tableau

/-- Keep a terminal configuration unchanged instead of introducing arbitrary
padding states. -/
def stutter {σ : Type*} (step : σ → Option σ) (c : σ) : σ := (step c).getD c

@[simp] theorem stutter_halt {σ : Type*} {step : σ → Option σ} {c : σ}
    (h : step c = none) : stutter step c = c := by simp [stutter,h]

/-- Every padding step preserves the same terminal configuration. -/
theorem stutter_iterate_halt {σ : Type*} {step : σ → Option σ} {c : σ}
    (h : step c = none) (t : ℕ) : (stutter step)^[t] c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, stutter_halt h]

/-- Accepted certificates with their complete deterministic histories. -/
abbrev AcceptedTableau {W σ : Type*} (next : σ → σ) (initial : W → σ)
    (time : ℕ) (accept : σ → Prop) :=
  {wt : (w : W) × Tableau next (initial w) time // accept (wt.2.state (Fin.last time))}

/-- A true bijection, rather than an existence-only tableau correctness claim. -/
def acceptedTableauEquiv {W σ : Type*} (next : σ → σ) (initial : W → σ)
    (time : ℕ) (accept : σ → Prop) :
    {w : W // accept (next^[time] (initial w))} ≃ AcceptedTableau next initial time accept where
  toFun w := ⟨⟨w.val,Tableau.canonical next (initial w.val) time⟩,w.property⟩
  invFun wt := ⟨wt.val.1, by simpa using wt.property⟩
  left_inv w := rfl
  right_inv wt := by
    rcases wt with ⟨⟨w,T⟩,h⟩
    have he := T.eq_canonical
    cases he
    rfl

noncomputable instance acceptedTableauFintype {W σ : Type*} [Fintype W]
    (next : σ → σ) (initial : W → σ) (time : ℕ) (accept : σ → Prop) :
    Fintype (AcceptedTableau next initial time accept) := by
  classical
  exact Fintype.ofEquiv {w : W // accept (next^[time] (initial w))}
    (acceptedTableauEquiv next initial time accept)

/-- No multiplicative factors arise from deterministic computation histories. -/
theorem acceptedTableau_card {W σ : Type*} [Fintype W]
    (next : σ → σ) (initial : W → σ) (time : ℕ) (accept : σ → Prop)
    [Fintype {w : W // accept (next^[time] (initial w))}] :
    Fintype.card (AcceptedTableau next initial time accept) =
    Fintype.card {w : W // accept (next^[time] (initial w))} :=
  Fintype.card_congr (acceptedTableauEquiv next initial time accept).symm

end HiddenCircuits.Complexity
