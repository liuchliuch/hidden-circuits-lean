import HiddenCircuits.Approximation.MonotoneStart
namespace HiddenCircuits.Approximation
open scoped BigOperators
section Restricted
variable {α : Type*} (P : α → Prop) [DecidablePred P] (f : α → α)
def restrictedMove (a : {a // P a}) : {a // P a} :=
  if h : P (f a.val) then ⟨f a.val,h⟩ else a
theorem restrictedMove_involutive (hf : Function.Involutive f) :
    Function.Involutive (restrictedMove P f) := by
  intro a
  by_cases h : P (f a.val)
  · apply Subtype.ext
    simp [restrictedMove,h,hf a.val,a.property]
  · simp [restrictedMove,h]
end Restricted
namespace MonotoneEndpoints
variable {n : ℕ} (E : MonotoneEndpoints n)
def transpose (π : Equiv.Perm (Fin n)) (i j : Fin n) : Equiv.Perm (Fin n) :=
  (Equiv.swap i j).trans π
@[simp] theorem transpose_apply (π : Equiv.Perm (Fin n)) (i j k : Fin n) :
    transpose π i j k = π (Equiv.swap i j k) := rfl
def switch (i j : Fin n) : E.Permutations → E.Permutations :=
  restrictedMove E.Admissible (fun π => transpose π i j)
theorem transpose_involutive (i j : Fin n) :
    Function.Involutive (fun π : Equiv.Perm (Fin n) => transpose π i j) := by
  intro π
  ext k
  simp [transpose]
theorem switch_involutive (i j : Fin n) : Function.Involutive (E.switch i j) :=
  restrictedMove_involutive E.Admissible _ (transpose_involutive i j)
@[simp] theorem switch_same (i : Fin n) (π : E.Permutations) : E.switch i i π = π := by
  apply Subtype.ext
  simp [switch,restrictedMove,transpose,π.property]
end MonotoneEndpoints
noncomputable def transitionProbability {α : Type*} (m : ℕ)
    (step : α → CoinTape m → α) (s t : α) : ℚ :=
  coinProbability m (fun r => step s r=t)
theorem transitionProbability_symmetric {α : Type*} (m : ℕ)
    (step : α → CoinTape m → α) (hstep : ∀ r, Function.Involutive (fun s => step s r))
    (s t : α) : transitionProbability m step s t = transitionProbability m step t s := by
  apply coinProbability_congr
  intro r
  constructor
  · intro h
    rw [← h]
    exact hstep r s
  · intro h
    rw [← h]
    exact hstep r t
theorem transitionProbability_sum {α : Type*} [Fintype α] (m : ℕ)
    (step : α → CoinTape m → α) (s : α) :
    ∑ t, transitionProbability m step s t = 1 := by
  classical
  unfold transitionProbability coinProbability
  simp_rw [Fintype.card_subtype,← Finset.sum_boole]
  rw [← Finset.sum_div,Finset.sum_comm]
  simp
theorem uniform_stationary {α : Type*} [Fintype α] [Nonempty α] (m : ℕ)
    (step : α → CoinTape m → α) (hstep : ∀ r, Function.Involutive (fun s => step s r))
    (t : α) :
    ∑ s, (1/(Fintype.card α : ℚ))*transitionProbability m step s t =
      1/(Fintype.card α : ℚ) := by
  simp_rw [transitionProbability_symmetric m step hstep _ t]
  rw [← Finset.mul_sum,transitionProbability_sum,mul_one]
end HiddenCircuits.Approximation
