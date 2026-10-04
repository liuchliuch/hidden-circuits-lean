import HiddenCircuits.Approximation.SamplerRuntime.PartnerBudget
import HiddenCircuits.Approximation.QuasimonotoneSampling

/-! Path length and probability-error bounds for the concrete quasimonotone paths. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerBudget
open QuasimonotoneProof FiniteChains GraphReduction Polynomial
attribute [local instance] Classical.propDecidable

noncomputable def paths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : Quasimonotone G)
    (N : ℕ) (hn : n≤N) : FiniteChains.CanonicalPaths (PartnerSwitch.chain G (Nat.size n))
      (traffic N+1) (length N+1) (8*(N+1)^2) where
  path := (quasimonotoneCanonicalPaths G hG).path
  length_le x y := ((quasimonotoneCanonicalPaths G hG).length_le x y).trans ((length_mono hn).trans (by omega))
  traffic_le x y := ((quasimonotoneCanonicalPaths G hG).traffic_le x y).trans
    (Nat.mul_le_mul_right _ ((traffic_mono hn).trans (by omega)))
  Q_pos := by positivity
  transition_lower x y i := by
    refine le_trans ?_ ((quasimonotoneCanonicalPaths G hG).transition_lower x y i)
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast (show 8*(n+1)^2≤8*(N+1)^2 by gcongr)

lemma paths_steps {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : Quasimonotone G)
    [Nonempty (PerfectPartner G)] (N : ℕ) (hn : n≤N) :
    (paths G hG N hn).mixingSteps (N^2) N=steps N := by
  rw [FiniteChains.CanonicalPaths.mixingSteps,FiniteChains.CanonicalPaths.scale]
  have hp : 0<(length N+1)*(8*(N+1)^2)*(traffic N+1) := by positivity
  rw [max_eq_right (by omega)]
  unfold steps
  ring

theorem event_error {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : Quasimonotone G)
    (s : PerfectPartner G) (N k : ℕ) (hn : n≤N) (hk : k≤N) (A : PerfectPartner G → Prop) :
    |coinProbability ((1+(Nat.size n+Nat.size n))*steps N)
      (fun r => A (runCoins (PartnerSwitch.step G (Nat.size n)) (steps N) s r))-
      (Fintype.card {x : PerfectPartner G // A x}:ℚ)/Fintype.card (PerfectPartner G)|≤1/(2^k:ℚ) := by
  letI : Nonempty (PerfectPartner G) := ⟨s⟩
  have hc : Fintype.card (PerfectPartner G)≤2^(N^2) :=
    (PartnerSwitch.card_states_le G).trans (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hn 2))
  have hh := runCoins_event_error (PartnerSwitch.step G (Nat.size n)) (PartnerSwitch.step_involutive G _)
    (PartnerSwitch.step_lazy G _) (paths G hG N hn) (N^2) N hc s A
  have ht := paths_steps G hG N hn
  rw [ht] at hh
  refine hh.trans ?_
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_right₀ (by norm_num) hk

end HiddenCircuits.Approximation.SamplerRuntime.PartnerBudget
