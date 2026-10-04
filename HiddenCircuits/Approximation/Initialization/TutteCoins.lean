import HiddenCircuits.Approximation.Initialization.TuttePolynomial
import HiddenCircuits.Approximation.FiniteChains.CoinTools
import HiddenCircuits.Approximation.SelfReduction.CoinExperiment

/-! Schwartz--Zippel for the actual finite fair-bit experiment.
Each variable is read from one disjoint fixed-width binary block. -/
namespace HiddenCircuits.Approximation.Initialization.TutteCoins
open scoped BigOperators
open FiniteChains SelfReduction

def draw (q m : ℕ) (r : CoinTape (q*m)) (i : Fin q) : ℚ :=
  (tapeNumber m (splitBlocks q m r i)).val

theorem draw_injective (q m : ℕ) : Function.Injective (draw q m) := by
  intro r s h
  apply (splitBlocks q m).injective
  funext i
  apply (tapeNumber m).injective
  apply Fin.ext
  have hh := congrFun h i
  unfold draw at hh
  exact_mod_cast hh

def samples (m : ℕ) : Finset ℚ := (Finset.range (2^m)).image (fun i : ℕ => (i : ℚ))

@[simp] theorem samples_card (m : ℕ) : (samples m).card = 2^m := by
  rw [samples, Finset.card_image_of_injective _ Nat.cast_injective]
  simp

theorem draw_mem (q m : ℕ) (r : CoinTape (q*m)) (i : Fin q) :
    draw q m r i ∈ samples m := by
  apply Finset.mem_image.mpr
  exact ⟨_, Finset.mem_range.mpr (tapeNumber m (splitBlocks q m r i)).isLt, rfl⟩

theorem false_zero_bound {q : ℕ} (p : MvPolynomial (Fin q) ℚ) (hp : p ≠ 0) (m : ℕ) :
    coinProbability (q*m) (fun r => MvPolynomial.eval (draw q m r) p = 0) ≤
      (p.totalDegree : ℚ) / (2^m : ℚ) := by
  classical
  let Z := (Fintype.piFinset (fun _ : Fin q => samples m)).filter
    (fun x => MvPolynomial.eval x p = 0)
  let f : {r : CoinTape (q*m) // MvPolynomial.eval (draw q m r) p = 0} → Z :=
    fun r => ⟨draw q m r.val, Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr (draw_mem q m r.val), r.property⟩⟩
  have hf : Function.Injective f := by
    intro r s h
    apply Subtype.ext
    exact draw_injective q m (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hc
  have hz := MvPolynomial.schwartz_zippel_totalDegree hp (samples m)
  simp only [samples_card] at hz
  have hz' : (Z.card : ℚ) / ((2^m : ℚ)^q) ≤ (p.totalDegree : ℚ)/(2^m : ℚ) := by
    exact_mod_cast hz
  calc
    _ ≤ (Z.card : ℚ)/(2^(q*m) : ℚ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = (Z.card : ℚ)/((2^m : ℚ)^q) := by rw [←pow_mul, Nat.mul_comm m q]
    _ ≤ _ := hz'

theorem graph_false_zero_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : Nonempty (PerfectMatching G)) (m : ℕ) :
    coinProbability (n*n*m)
      (fun r => (TuttePolynomial.matrix G (draw (n*n) m r)).det = 0) ≤
      (n : ℚ)/(2^m : ℚ) := by
  have hh := false_zero_bound (TuttePolynomial.polynomial G)
    (TuttePolynomial.polynomial_ne_zero G hG) m
  simp only [TuttePolynomial.eval_polynomial] at hh
  refine hh.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast TuttePolynomial.polynomial_degree G

end HiddenCircuits.Approximation.Initialization.TutteCoins
