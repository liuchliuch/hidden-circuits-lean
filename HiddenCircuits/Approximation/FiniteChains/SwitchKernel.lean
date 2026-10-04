import HiddenCircuits.Approximation.FiniteChains.CoinTools
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
def switchProposal (m : ℕ) : CoinTape (1+(m+m)) ≃ Bool × (Fin (2^m) × Fin (2^m)) :=
  (splitTape 1 (m+m)).trans
    (Equiv.prodCongr (Equiv.funUnique (Fin 1) Bool)
      ((splitTape m m).trans (Equiv.prodCongr (tapeNumber m) (tapeNumber m))))
namespace MonotoneSwitch
variable {n : ℕ} (E : MonotoneEndpoints n)
/-- A deterministic transition using exactly `1+2*m` fair bits. -/
def step (m : ℕ) (π : E.Permutations) (r : CoinTape (1+(m+m))) : E.Permutations :=
  let p := switchProposal m r
  if p.1 then π else
  if hi : p.2.1.val < n then
    if hj : p.2.2.val < n then E.switch ⟨p.2.1.val,hi⟩ ⟨p.2.2.val,hj⟩ π else π
  else π
theorem step_involutive (m : ℕ) (r : CoinTape (1+(m+m))) :
    Function.Involutive (fun π => step E m π r) := by
  intro π
  dsimp [step]
  split_ifs with h hi hj
  · rfl
  · exact E.switch_involutive _ _ π
  · rfl
  · rfl
theorem step_hold (m : ℕ) (π : E.Permutations) (r : CoinTape (1+(m+m)))
    (hr : (switchProposal m r).1=true) : step E m π r=π := by simp [step,hr]
theorem step_proposal (m : ℕ) (hm : n ≤ 2^m) (π : E.Permutations) (i j : Fin n) :
    step E m π ((switchProposal m).symm
      (false,(⟨i.val,lt_of_lt_of_le i.isLt hm⟩,⟨j.val,lt_of_lt_of_le j.isLt hm⟩))) =
      E.switch i j π := by
  simp [step,i.isLt,j.isLt]
/-- Exactly half the proposal tapes have their holding bit set. -/
theorem hold_probability (m : ℕ) :
    coinProbability (1+(m+m)) (fun r => (switchProposal m r).1=true) = (1:ℚ)/2 := by
  classical
  letI : DecidablePred (fun p : Bool × (Fin (2^m) × Fin (2^m)) => p.1=true) :=
    fun _ => Classical.propDecidable _
  rw [coinProbability_equiv (1+(m+m)) (switchProposal m) (fun p => p.1=true)]
  have e : {p : Bool × (Fin (2^m) × Fin (2^m)) // p.1=true} ≃
      (Fin (2^m) × Fin (2^m)) :=
    { toFun := fun p => p.val.2
      invFun := fun p => ⟨(true,p),rfl⟩
      left_inv := by intro p; apply Subtype.ext; exact Prod.ext p.property.symm rfl
      right_inv := by intro p; rfl }
  have hc : Fintype.card {p : Bool × (Fin (2^m) × Fin (2^m)) // p.1=true} =
      Fintype.card (Fin (2^m) × Fin (2^m)) := Fintype.card_congr e
  have hc' : (Fintype.card {p : Bool × (Fin (2^m) × Fin (2^m)) // p.1=true} : ℚ) /
      (2^(1+(m+m)) : ℚ) = Fintype.card (Fin (2^m) × Fin (2^m)) /
      (2^(1+(m+m)) : ℚ) := by exact congrArg (fun c : ℕ => (c:ℚ)/(2^(1+(m+m)):ℚ)) hc
  refine hc'.trans ?_
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [pow_add,pow_add,pow_one]
  field_simp
  <;> ring
theorem step_lazy (m : ℕ) (π : E.Permutations) :
    (1:ℚ)/2 ≤ transitionProbability (1+(m+m)) (step E m) π π := by
  rw [← hold_probability m]
  apply coinProbability_mono
  exact fun r hr => step_hold E m π r hr
noncomputable def chain (m : ℕ) : LazyChain E.Permutations :=
  LazyChain.ofCoinStep (1+(m+m)) (step E m) (step_involutive E m) (step_lazy E m)
theorem switch_probability_lower (m : ℕ) (hm : n ≤ 2^m) (π : E.Permutations) (i j : Fin n) :
    1/(2^(1+(m+m)) : ℚ) ≤
      transitionProbability (1+(m+m)) (step E m) π (E.switch i j π) := by
  exact reciprocal_le_coinProbability _ _ _ (step_proposal E m hm π i j)
/-- The fixed proposal width is logarithmic in the vertex count. -/
theorem proposal_width_covers : n ≤ 2^(Nat.size n) := (Nat.lt_size_self n).le
theorem inverse_probability_le (hn : 0<n) :
    2^(1+(Nat.size n+Nat.size n)) ≤ 8*n^2 := by
  have hs : 0<Nat.size n := by
    apply Nat.pos_of_ne_zero
    intro h
    have ht := Nat.lt_size_self n
    rw [h,pow_zero] at ht
    omega
  have hlow : 2^(Nat.size n-1) ≤ n := Nat.lt_size.mp (by omega)
  have hup : 2^Nat.size n ≤ 2*n := by
    have he : Nat.size n=(Nat.size n-1)+1 := by omega
    rw [he,pow_succ]
    omega
  rw [pow_add,pow_add,pow_one]
  have hsq := Nat.mul_le_mul hup hup
  nlinarith
/-- The edge lower bound in the real-valued chain analysis. -/
theorem chain_switch_lower (m : ℕ) (hm : n ≤ 2^m) (π : E.Permutations) (i j : Fin n) :
    (1:ℝ)/(2^(1+(m+m)) : ℕ) ≤ (chain E m).weight π (E.switch i j π) := by
  change (1:ℝ)/(2^(1+(m+m)) : ℕ) ≤
    (transitionProbability (1+(m+m)) (step E m) π (E.switch i j π) : ℝ)
  have h := (Rat.cast_le (K := ℝ)).mpr (switch_probability_lower E m hm π i j)
  push_cast at h ⊢
  exact h
theorem chain_switch_polynomial_lower (hn : 0<n) (π : E.Permutations) (i j : Fin n) :
    (1:ℝ)/(8*n^2 : ℕ) ≤ (chain E (Nat.size n)).weight π (E.switch i j π) := by
  have hl := chain_switch_lower E (Nat.size n) proposal_width_covers π i j
  refine le_trans ?_ hl
  apply one_div_le_one_div_of_le
  · exact_mod_cast (pow_pos (by decide : (0:ℕ)<2) (1+(Nat.size n+Nat.size n)))
  · exact_mod_cast inverse_probability_le hn
theorem chain_switch_polynomial_lower_all (π : E.Permutations) (i j : Fin n) :
    (1:ℝ)/(8*(n+1)^2 : ℕ) ≤ (chain E (Nat.size n)).weight π (E.switch i j π) := by
  have hn : 0<n := Nat.zero_lt_of_lt i.isLt
  refine le_trans ?_ (chain_switch_polynomial_lower E hn π i j)
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast (show 8*n^2 ≤ 8*(n+1)^2 by nlinarith)
/-- A feasible transposition is the accepted switch, with no rejection. -/
theorem switch_eq_of_transpose (π ρ : E.Permutations) (i j : Fin n)
    (h : ρ.val=(Equiv.swap i j).trans π.val) : E.switch i j π=ρ := by
  have hv : E.Admissible (MonotoneEndpoints.transpose π.val i j) := by
    simpa only [MonotoneEndpoints.transpose,← h] using ρ.property
  apply Subtype.ext
  simp [MonotoneEndpoints.switch,restrictedMove,MonotoneEndpoints.transpose,← h,ρ.property]
theorem chain_transpose_lower (π ρ : E.Permutations) (i j : Fin n)
    (h : ρ.val=(Equiv.swap i j).trans π.val) :
    (1:ℝ)/(8*(n+1)^2 : ℕ) ≤ (chain E (Nat.size n)).weight π ρ := by
  rw [← switch_eq_of_transpose E π ρ i j h]
  exact chain_switch_polynomial_lower_all E π i j
theorem card_states_le : Fintype.card E.Permutations ≤ 2^(n^2) := by
  have hi : Function.Injective (fun π : E.Permutations => (π.val : Fin n → Fin n)) := by
    intro π ρ h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact congrFun h i
  calc
    _ ≤ Fintype.card (Fin n → Fin n) := Fintype.card_le_of_injective _ hi
    _ = n^n := by simp
    _ ≤ (2^n)^n := Nat.pow_le_pow_left Nat.lt_two_pow_self.le n
    _ = _ := by rw [← pow_mul,pow_two]
theorem proposal_width_le : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
end MonotoneSwitch
end HiddenCircuits.Approximation.FiniteChains
