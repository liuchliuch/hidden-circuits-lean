import HiddenCircuits.Approximation.SelfReduction.FiniteMean

/-! Independent finite samples: exact centered second moment and Chebyshev.
No statistical assumption is substituted for the finite product calculation. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

 def sampleAverage {α : Type*} (n : ℕ) (X : α → ℚ) (r : Fin n → α) : ℚ :=
  (∑ i, X (r i))/(n : ℚ)

 theorem mean_sample_sum {α : Type*} [Fintype α] [Nonempty α] (X : α → ℚ) (n : ℕ) :
    mean (fun r : Fin n → α => ∑ i, X (r i))=(n : ℚ)*mean X := by
  induction n with
  | zero => simp [mean]
  | succ n ih =>
    rw [mean_fin_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [mean_add, mean_const]
    rw [ih]
    push_cast
    ring

 theorem mean_centered_sum_sq {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℚ) (hX : mean X=0) (n : ℕ) :
    mean (fun r : Fin n → α => (∑ i, X (r i))^2)=(n : ℚ)*mean (fun a => X a^2) := by
  induction n with
  | zero => simp [mean]
  | succ n ih =>
    rw [mean_fin_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hex (a : α) (r : Fin n → α) :
        (X a+∑ i, X (r i))^2=X a^2+(2*X a)*(∑ i, X (r i))+(∑ i, X (r i))^2 := by ring
    simp only [hex, mean_add, mean_const_mul, mean_const, mean_sample_sum, hX, mul_zero,
      add_zero, ih]
    push_cast
    ring

 theorem mean_centered_sq {α : Type*} [Fintype α] [Nonempty α] (X : α → ℚ) :
    mean (fun a => (X a-mean X)^2)=mean (fun a => X a^2)-(mean X)^2 := by
  have h (a : α) : (X a-mean X)^2=X a^2-2*mean X*X a+(mean X)^2 := by ring
  simp_rw [h, mean_add, mean_sub, mean_const_mul, mean_const]
  ring

 theorem mean_centered_sq_le_quarter {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℚ) (hX : ∀ a, 0 ≤ X a ∧ X a ≤ 1) :
    mean (fun a => (X a-mean X)^2) ≤ 1/4 := by
  rw [mean_centered_sq]
  have hh : mean (fun a => X a^2) ≤ mean X := mean_mono (fun a => by
    obtain ⟨ha,hb⟩ := hX a
    nlinarith)
  nlinarith [sq_nonneg (mean X-1/2)]

/-- The exact variance of a finite Bernoulli observation. -/
 theorem bernoulli_variance {α : Type*} [Fintype α] [Nonempty α]
    (E : α → Prop) [DecidablePred E] :
    mean (fun a => ((if E a then (1 : ℚ) else 0)-probability E)^2)=
      probability E*(1-probability E) := by
  have hp := mean_indicator E
  rw [← hp, mean_centered_sq]
  have hs : mean (fun a => (if E a then (1 : ℚ) else 0)^2)=
      mean (fun a => if E a then (1 : ℚ) else 0) := by
    apply mean_congr
    intro a
    split_ifs <;> norm_num
  rw [hs]
  ring

 theorem sampleAverage_variance {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℚ) (n : ℕ) (hn : 0<n) :
    mean (fun r : Fin n → α => (sampleAverage n X r-mean X)^2)=
      mean (fun a => (X a-mean X)^2)/(n : ℚ) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcenter : mean (fun a => X a-mean X)=0 := by rw [mean_sub, mean_const]; ring
  have he (r : Fin n → α) : sampleAverage n X r-mean X=
      (∑ i, (X (r i)-mean X))/(n : ℚ) := by
    simp only [sampleAverage, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [he, div_pow]
  rw [mean_div_const, mean_centered_sum_sq _ hcenter]
  field_simp

/-- Quantitative Chebyshev for genuinely independent uniform samples of a
bounded random variable. -/
 theorem sampleAverage_chebyshev {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℚ) (hX : ∀ a, 0 ≤ X a ∧ X a ≤ 1) (n : ℕ) (hn : 0<n)
    (ε : ℚ) (hε : 0<ε) :
    probability (fun r : Fin n → α => ε < |sampleAverage n X r-mean X|) ≤ 1/(4*n*ε^2) := by
  have hm := probability_markov (fun r : Fin n → α => (sampleAverage n X r-mean X)^2)
    (fun _ => sq_nonneg _) (ε^2) (sq_pos_of_pos hε)
  have hs : probability (fun r : Fin n → α => ε < |sampleAverage n X r-mean X|) ≤ 
      probability (fun r : Fin n → α => ε^2 ≤ (sampleAverage n X r-mean X)^2) := by
    apply probability_mono
    intro r hr
    nlinarith [sq_abs (sampleAverage n X r-mean X)]
  apply hs.trans (hm.trans _)
  rw [sampleAverage_variance X n hn]
  calc
    _  ≤  (1/4/(n : ℚ))/ε^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact div_le_div_of_nonneg_right (mean_centered_sq_le_quarter X hX) (Nat.cast_nonneg _)
    _ = _ := by ring

end HiddenCircuits.Approximation.SelfReduction
