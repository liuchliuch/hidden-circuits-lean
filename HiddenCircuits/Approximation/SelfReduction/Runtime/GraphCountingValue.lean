import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountUniform
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountParity
import HiddenCircuits.Approximation.SelfReduction.Runtime.ListTape

/-! Typed even-input bridge and exact estimator value on one padded physical
fair tape. Odd-order rejection is handled by the outer raw-input machine. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity SelfReduction.GraphCount

def castMatrix {n m : ℕ} (G : MatrixGraph n) (h : n=m) : MatrixGraph m := h ▸ G
lemma castMatrix_input {n m : ℕ} (G : MatrixGraph n) (h : n=m) :
    (⟨m,castMatrix G h⟩ : GraphInput)=⟨n,G⟩ := by cases h; rfl
lemma castMatrix_count {n m : ℕ} (G : MatrixGraph n) (h : n=m) :
    perfectMatchingCount (castMatrix G h).graph=perfectMatchingCount G.graph := by cases h; rfl
lemma castMatrix_promised {n m : ℕ} (G : MatrixGraph n) (h : n=m)
    (hc : Quasimonotone G.graph) : Quasimonotone (castMatrix G h).graph := by cases h; exact hc

def evenMatrix (G : GraphInput) (he : G.1%2=0) : MatrixGraph (2*(G.1/2)) :=
  castMatrix G.2 (half_vertices G.1 he).symm
@[simp] lemma evenMatrix_input (G : GraphInput) (he : G.1%2=0) :
    (⟨2*(G.1/2),evenMatrix G he⟩ : GraphInput)=G := castMatrix_input G.2 _
@[simp] lemma evenMatrix_count (G : GraphInput) (he : G.1%2=0) :
    perfectMatchingCount (evenMatrix G he).graph=perfectMatchingCount G.2.graph := castMatrix_count G.2 _
lemma evenMatrix_promised (G : GraphInput) (he : G.1%2=0) (hc : Quasimonotone G.2.graph) :
    Quasimonotone (evenMatrix G he).graph := castMatrix_promised G.2 _ hc

lemma even_bound (N : ℕ) (G : GraphInput) (he : G.1%2=0) (hd : G.1≤N) : 2*(G.1/2)≤N+1 := by
  rw [half_vertices G.1 he]
  omega

noncomputable def estimate (N : ℕ) (G : GraphInput) (he : G.1%2=0) (hd : G.1≤N) (coins : BitString) : BitString :=
  let m := uniformSampleBitsPolynomial.eval N
  uniformOutput N m (G.1/2) ⟨G.1/2,some ⟨evenMatrix G he,even_bound N G he hd⟩⟩
    (tapeOfList (countingBits m (uniformAccuracy N) (uniformConfidence N) (G.1/2)) coins)

lemma estimate_zero (N : ℕ) (G : GraphInput) (he : G.1%2=0) (hd : G.1≤N)
    (hz : perfectMatchingCount G.2.graph=0) (coins : BitString) :
    decodeEstimate (estimate N G he hd coins)=some 0 := by
  unfold estimate uniformOutput
  exact shortOutput_zero _ _ _ _ _ _ rfl (by simpa only [count_active,evenMatrix_count] using hz) _

lemma estimate_guarantee (N : ℕ) (G : GraphInput) (he : G.1%2=0) (hd : G.1≤N)
    (hclass : Quasimonotone G.2.graph) (r k : ℕ) (hr : r≤N) (hk : k≤N) :
    1-1/(2^k : ℚ)≤coinProbability (randomBitsPolynomial.eval N)
      (fun tape => ∃z,decodeEstimate (estimate N G he hd (List.ofFn tape))=some z ∧
        RelativeEstimate (perfectMatchingCount G.2.graph) r z) := by
  have hdepth := half_vertices_le G.1 N hd
  have hf := (uniformOutput_guarantee (b:=N) N (uniformSampleBitsPolynomial.eval N) (G.1/2) r k
    (le_refl N) hdepth hr hk (uniformSampleBits_sufficient N (le_refl N))
    ⟨G.1/2,some ⟨evenMatrix G he,even_bound N G he hd⟩⟩ (evenMatrix_promised G he hclass) rfl).2
  simp only [count_active,evenMatrix_count] at hf
  have hbits := countingBits_polynomial_bound N (G.1/2) hdepth
  unfold estimate
  simp_rw [tapeOfList_ofFn_restrict hbits]
  rw [SamplerRuntime.CoinLists.probability_restrict hbits (fun tape => ∃z,
    decodeEstimate (uniformOutput N (uniformSampleBitsPolynomial.eval N) (G.1/2)
      ⟨G.1/2,some ⟨evenMatrix G he,even_bound N G he hd⟩⟩ tape)=some z ∧
      RelativeEstimate (perfectMatchingCount G.2.graph) r z)]
  exact hf

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
