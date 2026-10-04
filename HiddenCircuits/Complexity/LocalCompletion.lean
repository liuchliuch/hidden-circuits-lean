import HiddenCircuits.Complexity.LocalNetworkCNF
import HiddenCircuits.Complexity.OneHot

/-! Constructive finite-port completion: a local Boolean transition is obtained
from its explicit fixed-width port list without assuming a circuit or CNF compiler. -/
namespace HiddenCircuits.Complexity

lemma scanTrue_none_iff {α : Type*} (as : List α) (w : α → Bool) :
    scanTrue as w = none ↔ ∀ a ∈ as, w a = false := by
  induction as with
  | nil => simp [scanTrue]
  | cons a as ih =>
    cases h : w a <;> simp [scanTrue,h,ih]

lemma scanTrue_some_sound {α : Type*} (as : List α) (w : α → Bool) (a : α)
    (h : scanTrue as w = some a) : a ∈ as ∧ w a = true := by
  induction as with
  | nil => simp [scanTrue] at h
  | cons b bs ih =>
    cases hb : w b with
    | false =>
      have ht : scanTrue bs w = some a := by simpa [scanTrue,hb] using h
      have ha := ih ht
      exact ⟨List.mem_cons_of_mem _ ha.1,ha.2⟩
    | true =>
      have he : b = a := by simpa [scanTrue,hb] using h
      subst b
      exact ⟨by simp,hb⟩

noncomputable def sparseComplete {V P : Type*} [Fintype P] [DecidableEq V]
    (ports : P → V) (values : P → Bool) (v : V) : Bool :=
  match scanTrue Finset.univ.toList (fun p => decide (ports p = v)) with
  | none => false
  | some p => values p

/-- Duplicate port addresses are harmless when values are read from an actual assignment. -/
theorem sparseComplete_read {V P : Type*} [Fintype P] [DecidableEq V]
    (ports : P → V) (w : V → Bool) (p : P) :
    sparseComplete ports (fun q => w (ports q)) (ports p) = w (ports p) := by
  unfold sparseComplete
  cases h : scanTrue Finset.univ.toList (fun q => decide (ports q = ports p)) with
  | none =>
    have hn := (scanTrue_none_iff _ _).mp h p (by simp)
    simp at hn
  | some q =>
    have hs := (scanTrue_some_sound _ _ q h).2
    exact congrArg w (of_decide_eq_true hs)

noncomputable def compileLocal {n r : ℕ} (F : (Fin n → Bool) → Fin n → Bool)
    (ports : Fin n → Fin r → Fin n) : LocalNetwork n r where
  ports := ports
  rule v values := F (sparseComplete (ports v) values) v

/-- The compiler's premise is an ordinary data-dependence theorem, not a promised
running time or counting hardness; it is proved for actual TM2 transitions separately. -/
theorem compileLocal_correct {n r : ℕ} (F : (Fin n → Bool) → Fin n → Bool)
    (ports : Fin n → Fin r → Fin n)
    (hdep : ∀ v w z, (∀ p, w (ports v p) = z (ports v p)) → F w v = F z v)
    (w : Fin n → Bool) : (compileLocal F ports).step w = F w := by
  funext v
  apply hdep
  intro p
  exact sparseComplete_read (ports v) w p

end HiddenCircuits.Complexity
