import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphFPRAS

/-! New proof: the existing physical graph counter can consume a longer fair
tape. Its estimator reads a fixed prefix; the finite restriction map preserves
exact probabilities, including failures and zero/empty instances. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity SelfReduction.GraphCount

lemma estimate_guarantee_padded (N : ℕ) (G : GraphInput) (he : G.1%2=0) (hd : G.1≤N)
    (hclass : Quasimonotone G.2.graph) (r k : ℕ) (hr : r≤N) (hk : k≤N) (m : ℕ)
    (hm : randomBitsPolynomial.eval N ≤ m) :
    1-1/(2^k : ℚ)≤coinProbability m
      (fun tape => ∃z,decodeEstimate (estimate N G he hd (List.ofFn tape))=some z ∧
        RelativeEstimate (perfectMatchingCount G.2.graph) r z) := by
  have hdepth:=half_vertices_le G.1 N hd
  have hf:=(uniformOutput_guarantee (b:=N) N (uniformSampleBitsPolynomial.eval N) (G.1/2) r k
    (le_refl N) hdepth hr hk (uniformSampleBits_sufficient N (le_refl N))
    ⟨G.1/2,some ⟨evenMatrix G he,even_bound N G he hd⟩⟩ (evenMatrix_promised G he hclass) rfl).2
  simp only [count_active,evenMatrix_count] at hf
  have hbits:=(countingBits_polynomial_bound N (G.1/2) hdepth).trans hm
  unfold estimate
  simp_rw [tapeOfList_ofFn_restrict hbits]
  rw [SamplerRuntime.CoinLists.probability_restrict hbits (fun tape=>∃z,
    decodeEstimate (uniformOutput N (uniformSampleBitsPolynomial.eval N) (G.1/2)
      ⟨G.1/2,some ⟨evenMatrix G he,even_bound N G he hd⟩⟩ tape)=some z ∧
      RelativeEstimate (perfectMatchingCount G.2.graph) r z)]
  exact hf

lemma evaluate_zero_padded (G : GraphInput) (r k : ℕ) (coins : BitString)
    (hz : perfectMatchingCount G.2.graph=0)
    (hcoins : randomBitsPolynomial.eval (estimateInput G.encode r k).length≤coins.length) :
    decodeEstimate (evaluate (pairBits (estimateInput G.encode r k) coins))=some 0 := by
  by_cases he:G.1%2=0
  · rw [evaluate_canonical G r k coins he hcoins]
    exact estimate_zero _ G he (GraphCountSetup.canonical_bounds G r k).1 hz coins
  · rw [evaluate_odd G r k coins he]
    simp

lemma evaluate_empty_padded (G : GraphInput) (hG:G.1=0) (r k : ℕ) (coins : BitString)
    (hcoins : randomBitsPolynomial.eval (estimateInput G.encode r k).length≤coins.length) :
    decodeEstimate (evaluate (pairBits (estimateInput G.encode r k) coins))=some 1 := by
  rcases G with ⟨n,G⟩
  change n=0 at hG
  subst n
  rw [evaluate_canonical ⟨0,G⟩ r k coins (by rfl) hcoins]
  simp [estimate,uniformOutput,shortOutput,shortCounts,reciprocalProductOutput]

lemma evaluate_guarantee_padded (G : GraphInput) (hclass : Quasimonotone G.2.graph) (r k m : ℕ)
    (hm : randomBitsPolynomial.eval (estimateInput G.encode r k).length ≤ m) :
    1-1/(2^k:ℚ)≤coinProbability m (fun tape=>∃z,
      decodeEstimate (evaluate (pairBits (estimateInput G.encode r k) (List.ofFn tape)))=some z ∧
        RelativeEstimate (perfectMatchingCount G.2.graph) r z) := by
  by_cases he:G.1%2=0
  · have hc (tape : CoinTape m) := evaluate_canonical G r k (List.ofFn tape) he
      (by simpa only [List.length_ofFn] using hm)
    simp_rw [hc]
    have hb:=GraphCountSetup.canonical_bounds G r k
    exact estimate_guarantee_padded _ G he hb.1 hclass r k hb.2.1 hb.2.2 m hm
  · have hz:=perfectMatchingCount_zero_of_odd G.2.graph he
    have hh : (fun tape : CoinTape m=>∃z,
        decodeEstimate (evaluate (pairBits (estimateInput G.encode r k) (List.ofFn tape)))=some z ∧
          RelativeEstimate (perfectMatchingCount G.2.graph) r z)=(fun _=>True) := by
      funext tape;apply propext;simp [evaluate_odd G r k _ he,hz]
    rw [hh,coinProbability_true]
    have hp:(0:ℚ)≤1/2^k:=by positivity
    linarith

lemma raw_program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃t,program.Executes g (Function.update (fun _ : Fin 107=>[]) 0 raw)
      (Function.update (fun _ : Fin 107=>[]) 0 (evaluate raw)) t ∧t≤time.eval raw.length := by
  obtain ⟨t,ht,hb⟩:=program_executes g raw
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> rfl
end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
