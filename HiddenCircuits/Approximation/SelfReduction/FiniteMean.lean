import Mathlib

/-! Finite uniform averages and probabilities, reconstructed after the source
reset. All laws below are proved from finite sums. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

noncomputable def mean {α : Type*} [Fintype α] (f : α → ℚ) : ℚ :=
  (∑ a, f a) / Fintype.card α

noncomputable def probability {α : Type*} [Fintype α] (E : α → Prop) : ℚ := by
  classical
  exact mean (fun a => if E a then 1 else 0)

 theorem mean_congr {α : Type*} [Fintype α] {f g : α → ℚ} (h : ∀ a, f a=g a) : mean f=mean g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

 theorem mean_indicator {α : Type*} [Fintype α] (E : α → Prop) [DecidablePred E] :
    mean (fun a => if E a then (1 : ℚ) else 0)=probability E := by
  classical
  unfold probability
  apply mean_congr
  intro a
  by_cases h : E a <;> simp [h]

 theorem mean_mono {α : Type*} [Fintype α] {f g : α → ℚ} (h : ∀ a, f a ≤ g a) : mean f ≤ mean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

 theorem mean_nonneg {α : Type*} [Fintype α] {f : α → ℚ} (h : ∀ a, 0 ≤ f a) : 0 ≤ mean f := by
  unfold mean
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (Nat.cast_nonneg _)

@[simp] theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℚ) : mean (fun _ : α => c)=c := by
  have hc : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hc]

 theorem mean_add {α : Type*} [Fintype α] (f g : α → ℚ) :
    mean (fun a => f a+g a)=mean f+mean g := by simp [mean, Finset.sum_add_distrib, add_div]
 theorem mean_sub {α : Type*} [Fintype α] (f g : α → ℚ) :
    mean (fun a => f a-g a)=mean f-mean g := by simp [mean, Finset.sum_sub_distrib, sub_div]
 theorem mean_mul_const {α : Type*} [Fintype α] (f : α → ℚ) (c : ℚ) :
    mean (fun a => f a*c)=mean f*c := by unfold mean; rw [← Finset.sum_mul]; ring
 theorem mean_const_mul {α : Type*} [Fintype α] (c : ℚ) (f : α → ℚ) :
    mean (fun a => c*f a)=c*mean f := by unfold mean; rw [← Finset.mul_sum]; ring
 theorem mean_div_const {α : Type*} [Fintype α] (f : α → ℚ) (c : ℚ) :
    mean (fun a => f a/c)=mean f/c := by unfold mean; rw [← Finset.sum_div]; ring
 theorem mean_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℚ) :
    mean (fun a => ∑ i ∈ s, f i a)=∑ i ∈ s, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

 theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℚ) :
    mean (fun a => f (e a))=mean f := by
  unfold mean
  rw [Fintype.card_congr e, Equiv.sum_comp]

 theorem mean_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℚ) :
    mean f=mean (fun a => mean (fun b => f (a,b))) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.sum_div]
  ring

 theorem mean_prod_mul {α β : Type*} [Fintype α] [Fintype β] (f : α → ℚ) (g : β → ℚ) :
    mean (fun p : α × β => f p.1*g p.2)=mean f*mean g := by
  rw [mean_prod]
  simp_rw [mean_const_mul]
  exact mean_mul_const f (mean g)

 theorem mean_pi_prod {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] (f : ι → α → ℚ) :
    mean (fun r : ι → α => ∏ i, f i (r i))=∏ i, mean (f i) := by
  classical
  simp only [mean, Fintype.card_fun, Nat.cast_pow, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ]
  congr 1
  exact (Fintype.prod_sum f).symm

 theorem mean_fin_succ {α : Type*} [Fintype α] (n : ℕ) (f : (Fin (n+1) → α) → ℚ) :
    mean f=mean (fun a => mean (fun r : Fin n → α => f (Fin.cons a r))) := by
  rw [← mean_equiv (Fin.consEquiv (fun _ => α)) f, mean_prod]
  rfl

 theorem probability_nonneg {α : Type*} [Fintype α] (E : α → Prop) : 0 ≤ probability E := by
  classical
  apply mean_nonneg
  intro a
  split_ifs <;> norm_num

 theorem probability_mono {α : Type*} [Fintype α] {E F : α → Prop} (h : ∀ a, E a → F a) :
    probability E  ≤  probability F := by
  classical
  apply mean_mono
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp_all

 theorem probability_congr {α : Type*} [Fintype α] {E F : α → Prop} (h : ∀ a, E a ↔ F a) :
    probability E = probability F := le_antisymm (probability_mono (fun a => (h a).mp))
      (probability_mono (fun a => (h a).mpr))

@[simp] theorem probability_true {α : Type*} [Fintype α] [Nonempty α] : probability (fun _ : α => True)=1 := by
  simp [probability]
@[simp] theorem probability_false {α : Type*} [Fintype α] : probability (fun _ : α => False)=0 := by
  simp [probability, mean]
 theorem probability_le_one {α : Type*} [Fintype α] [Nonempty α] (E : α → Prop) : probability E ≤ 1 := by
  simpa using probability_mono (E := E) (F := fun _ => True) (fun _ _ => True.intro)
 theorem probability_compl {α : Type*} [Fintype α] [Nonempty α] (E : α → Prop) :
    probability (fun a => ¬E a)=1-probability E := by
  classical
  unfold probability
  calc
    _ = mean (fun a => 1-(if E a then 1 else 0)) := mean_congr (fun a => by by_cases h : E a <;> simp [h])
    _ = _ := by rw [mean_sub, mean_const]

 theorem probability_or {α : Type*} [Fintype α] (E F : α → Prop) :
    probability (fun a => E a ∨ F a) ≤ probability E+probability F := by
  classical
  unfold probability
  rw [← mean_add]
  apply mean_mono
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp [he,hf]

 theorem probability_exists {α ι : Type*} [Fintype α] [Fintype ι] (E : ι → α → Prop) :
    probability (fun a => ∃ i, E i a) ≤ ∑ i, probability (E i) := by
  classical
  unfold probability
  rw [← mean_sum]
  apply mean_mono
  intro a
  split_ifs with h
  · obtain ⟨i,hi⟩ := h
    exact (by simp [hi] : (1:ℚ)=(if E i a then 1 else 0)).trans_le
      (Finset.single_le_sum (f := fun j => (if E j a then 1 else 0 : ℚ)) (fun j _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ i))
  · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

/-- Finite Markov inequality, proved directly by comparing every summand. -/
 theorem probability_markov {α : Type*} [Fintype α] (f : α → ℚ)
    (hf : ∀ a, 0 ≤ f a) (t : ℚ) (ht : 0<t) :
    probability (fun a => t ≤ f a) ≤ mean f/t := by
  classical
  apply (le_div_iff₀ ht).2
  unfold probability
  rw [← mean_mul_const]
  apply mean_mono
  intro a
  split_ifs with h
  · simpa using h
  · simpa using hf a

end HiddenCircuits.Approximation.SelfReduction
