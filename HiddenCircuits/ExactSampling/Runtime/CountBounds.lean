import HiddenCircuits.ExactSampling.DHPaths
import HiddenCircuits.Complexity.PolynomialBounds

namespace HiddenCircuits.ExactSampling.Runtime
open Complexity DH DHWeights

 theorem count_word_length (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) :
    (Computability.encodeNat (count G)).length≤G.encode.length+BinaryRuntime.time.eval G.encode.length := by
  obtain ⟨t,ht,hb⟩ := BinaryRuntime.executes (fun _=>0) G.encode
  have hs := ht.stack_bound (n:=G.encode.length) (by
    intro i
    change (Function.update (fun _ : Fin 54 => ([]:BitString)) 0 G.encode i).length≤G.encode.length
    by_cases hi:i=(0:Fin 54) <;> simp only [Function.update_apply,hi,ite_true,ite_false,List.length_nil] <;> omega)
  have hh := hs (0:Fin 54)
  change (BinaryRuntime.function G.encode).length≤G.encode.length+t at hh
  rw [BinaryRuntime.distanceHereditary G hG,←count_correct G hG] at hh
  omega

 theorem rank_size_bound (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph)
    (x : Fin (count G)) : Nat.size x.val≤G.encode.length+BinaryRuntime.time.eval G.encode.length := by
  have hs := Nat.size_le_size x.isLt.le
  have hh := count_word_length G hG
  rw [encodeNat_length] at hh
  omega

 theorem residual_input_length {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    (Approximation.SelfReduction.Runtime.GraphResidual.output G j).length≤(GraphInput.encode ⟨N+1,G⟩).length := by
  open Approximation.SelfReduction.Runtime in
  have hj : (GraphResidual.retained j).card≤N+1 := by
    apply (Finset.card_le_card (Finset.subset_univ _)).trans
    simp
  simp only [Approximation.SelfReduction.Runtime.GraphResidual.output,GraphInput.encode_length]
  nlinarith [Nat.mul_le_mul hj hj]

end HiddenCircuits.ExactSampling.Runtime
