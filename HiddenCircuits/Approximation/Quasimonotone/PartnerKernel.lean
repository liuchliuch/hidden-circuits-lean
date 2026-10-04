import HiddenCircuits.Approximation.Quasimonotone.PartnerSwitch
import HiddenCircuits.Approximation.FiniteChains.CoinRealization
namespace HiddenCircuits.Approximation.QuasimonotoneProof.PartnerSwitch
open FiniteChains
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
/-- A deterministic transition using exactly `1+2*m` fair bits. -/
def step (m : ℕ) (π : PerfectPartner G) (r : CoinTape (1+(m+m))) : PerfectPartner G :=
  let p := switchProposal m r
  if p.1 then π else
  if hi : p.2.1.val < n then
    if hj : p.2.2.val < n then switch G ⟨p.2.1.val,hi⟩ ⟨p.2.2.val,hj⟩ π else π
  else π
theorem step_involutive (m : ℕ) (r : CoinTape (1+(m+m))) :
    Function.Involutive (fun π => step G m π r) := by
  intro π
  dsimp [step]
  split_ifs with h hi hj
  · rfl
  · exact switch_involutive G _ _ π
  · rfl
  · rfl
theorem step_hold (m : ℕ) (π : PerfectPartner G) (r : CoinTape (1+(m+m)))
    (hr : (switchProposal m r).1=true) : step G m π r=π := by simp [step,hr]
theorem step_proposal (m : ℕ) (hm : n ≤ 2^m) (π : PerfectPartner G) (i j : Fin n) :
    step G m π ((switchProposal m).symm
      (false,(⟨i.val,lt_of_lt_of_le i.isLt hm⟩,⟨j.val,lt_of_lt_of_le j.isLt hm⟩))) =
      switch G i j π := by
  simp [step,i.isLt,j.isLt]
theorem step_lazy (m : ℕ) (π : PerfectPartner G) :
    (1:ℚ)/2 ≤ transitionProbability (1+(m+m)) (step G m) π π := by
  rw [← MonotoneSwitch.hold_probability m]
  apply coinProbability_mono
  exact fun r hr => step_hold G m π r hr
noncomputable def chain (m : ℕ) : LazyChain (PerfectPartner G) :=
  LazyChain.ofCoinStep (1+(m+m)) (step G m) (step_involutive G m) (step_lazy G m)
theorem switch_probability_lower (m : ℕ) (hm : n ≤ 2^m) (π : PerfectPartner G) (i j : Fin n) :
    1/(2^(1+(m+m)) : ℚ) ≤
      transitionProbability (1+(m+m)) (step G m) π (switch G i j π) := by
  exact reciprocal_le_coinProbability _ _ _ (step_proposal G m hm π i j)
/-- The edge lower bound in the real-valued chain analysis. -/
theorem chain_switch_lower (m : ℕ) (hm : n ≤ 2^m) (π : PerfectPartner G) (i j : Fin n) :
    (1:ℝ)/(2^(1+(m+m)) : ℕ) ≤ (chain G m).weight π (switch G i j π) := by
  change (1:ℝ)/(2^(1+(m+m)) : ℕ) ≤
    (transitionProbability (1+(m+m)) (step G m) π (switch G i j π) : ℝ)
  have h := (Rat.cast_le (K := ℝ)).mpr (switch_probability_lower G m hm π i j)
  push_cast at h ⊢
  exact h
theorem chain_switch_polynomial_lower (hn : 0<n) (π : PerfectPartner G) (i j : Fin n) :
    (1:ℝ)/(8*n^2 : ℕ) ≤ (chain G (Nat.size n)).weight π (switch G i j π) := by
  have hl := chain_switch_lower G (Nat.size n) MonotoneSwitch.proposal_width_covers π i j
  refine le_trans ?_ hl
  apply one_div_le_one_div_of_le
  · exact_mod_cast (pow_pos (by decide : (0:ℕ)<2) (1+(Nat.size n+Nat.size n)))
  · exact_mod_cast MonotoneSwitch.inverse_probability_le hn
theorem chain_switch_polynomial_lower_all (π : PerfectPartner G) (i j : Fin n) :
    (1:ℝ)/(8*(n+1)^2 : ℕ) ≤ (chain G (Nat.size n)).weight π (switch G i j π) := by
  have hn : 0<n := Nat.zero_lt_of_lt i.isLt
  refine le_trans ?_ (chain_switch_polynomial_lower G hn π i j)
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast (show 8*n^2 ≤ 8*(n+1)^2 by nlinarith)
theorem move_chain_lower {P Q : PerfectPartner G} (h : PartnerMove P Q) :
    (1:ℝ)/(8*(n+1)^2 : ℕ) ≤ (chain G (Nat.size n)).weight P Q := by
  obtain ⟨a,b,h⟩ := move_switch G h
  rw [← h]
  exact chain_switch_polynomial_lower_all G P a b

theorem card_states_le : Fintype.card (PerfectPartner G) ≤ 2^(n^2) := by
  classical
  calc
    _ ≤ Fintype.card (Fin n → Fin n) := Fintype.card_le_of_injective (fun P : PerfectPartner G => P.val) (fun _ _ h => Subtype.ext h)
    _ = n^n := by simp
    _ ≤ (2^n)^n := Nat.pow_le_pow_left Nat.lt_two_pow_self.le n
    _ = _ := by rw [← pow_mul,pow_two]

end HiddenCircuits.Approximation.QuasimonotoneProof.PartnerSwitch
