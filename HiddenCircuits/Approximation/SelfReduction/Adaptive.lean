import HiddenCircuits.Approximation.SelfReduction.FiniteMean

/-! A finite product union bound along an adaptive state trajectory. The next
state may depend on all previously exposed samples, but not on fresh samples. -/
namespace HiddenCircuits.Approximation.SelfReduction

 def goodRun {S α : Type*} (step : S → α → S) (good : S → α → Prop) :
    (d : ℕ) → S → (Fin d → α) → Prop
  | 0, _, _ => True
  | d+1, s, r => good s (r 0) ∧ goodRun step good d (step s (r 0)) (fun i => r i.succ)

 theorem probability_fin_succ {α : Type*} [Fintype α] (n : ℕ)
    (E : (Fin (n+1) → α) → Prop) :
    probability E=mean (fun a => probability (fun r : Fin n → α => E (Fin.cons a r))) := by
  classical
  unfold probability
  exact mean_fin_succ n _

 theorem adaptive_rank_failure_bound {S α : Type*} [Fintype α] [Nonempty α]
    (step : S → α → S) (good : S → α → Prop) (P : S → Prop) (rank : S → ℕ)
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hlocal : ∀ s, P s → 0<rank s → probability (fun a => ¬good s a) ≤ δ)
    (hpreserve : ∀ s a, P s → good s a → P (step s a))
    (hrank : ∀ s a, P s → good s a → rank (step s a)+1=rank s)
    (d : ℕ) (s : S) (hs : P s) (hr : rank s=d) :
    probability (fun tape => ¬goodRun step good d s tape) ≤ (d : ℚ)*δ := by
  classical
  induction d generalizing s with
  | zero => simp [goodRun]
  | succ d ih =>
    rw [probability_fin_succ]
    have hb (a : α) :
        probability (fun r : Fin d → α => ¬goodRun step good (d+1) s (Fin.cons a r)) ≤
          (if ¬good s a then 1 else 0)+(d : ℚ)*δ := by
      by_cases hg : good s a
      · have hrs : rank (step s a)=d := by have hh := hrank s a hs hg; omega
        have ht := ih (step s a) (hpreserve s a hs hg) hrs
        simpa [goodRun,hg] using ht
      · simp only [goodRun, Fin.cons_zero, hg, false_and, not_false_eq_true,
          probability_true, not_false_eq_true, if_true]
        exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ)
    apply (mean_mono hb).trans
    rw [mean_add, mean_const, mean_indicator]
    have hh := hlocal s hs (by omega)
    push_cast
    linarith

end HiddenCircuits.Approximation.SelfReduction
