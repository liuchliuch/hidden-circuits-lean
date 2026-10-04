import HiddenCircuits.Approximation.SelfReduction.Runtime.ListTape
import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualPolynomial

/-! The exact endpoint estimator value realized by the counting core, including
its fixed global fair-tape padding and unconditional finite probability law. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity GraphReduction.MonotoneEndpointEncoding
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

noncomputable def endpointEstimate (N : ℕ) (E : Input) (hd : E.1 ≤ N) (coins : BitString) : BitString :=
  let m := uniformSampleBitsPolynomial.eval N
  uniformOutput N m E.1 ⟨E.1,some ⟨E.2,hd.trans (Nat.le_succ N)⟩⟩
    (tapeOfList (countingBits m (uniformAccuracy N) (uniformConfidence N) E.1) coins)

 theorem endpointEstimate_zero (N : ℕ) (E : Input) (hd : E.1 ≤ N)
    (hz : Fintype.card E.2.Permutations=0) (coins : BitString) :
    decodeEstimate (endpointEstimate N E hd coins)=some 0 := by
  have h := (polynomial_uniform_guarantee (b:=N) N E.1 0 0 (le_refl N) hd (Nat.zero_le _) (Nat.zero_le _)
    ⟨E.1,some ⟨E.2,hd.trans (Nat.le_succ N)⟩⟩ rfl).1
  exact h hz _

 theorem endpointEstimate_guarantee (N : ℕ) (E : Input) (hd : E.1 ≤ N) (r k : ℕ)
    (hr : r ≤ N) (hk : k ≤ N) :
    1-1/(2^k : ℚ) ≤ coinProbability (randomBitsPolynomial.eval N)
      (fun tape => ∃ z, decodeEstimate (endpointEstimate N E hd (List.ofFn tape))=some z ∧
        RelativeEstimate (Fintype.card E.2.Permutations) r z) := by
  have hf := (polynomial_uniform_guarantee (b:=N) N E.1 r k (le_refl N) hd hr hk
    ⟨E.1,some ⟨E.2,hd.trans (Nat.le_succ N)⟩⟩ rfl).2
  have hbits := countingBits_polynomial_bound N E.1 hd
  unfold endpointEstimate
  simp_rw [tapeOfList_ofFn_restrict hbits]
  rw [SamplerRuntime.CoinLists.probability_restrict hbits (fun tape => ∃ z,
    decodeEstimate (uniformOutput N (uniformSampleBitsPolynomial.eval N) E.1
      ⟨E.1,some ⟨E.2,hd.trans (Nat.le_succ N)⟩⟩ tape)=some z ∧
      RelativeEstimate (Fintype.card E.2.Permutations) r z)]
  exact hf

end HiddenCircuits.Approximation.SelfReduction.Runtime
