import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingCore
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingPolynomial
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingValue

/-! The actual core on globally padded bits, with fixed original-input budgets. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity SelfReduction.GraphCount

noncomputable def uniformInitial (N : ℕ) (G : GraphInput) (coins : BitString) : Complexity.OracleBlock.Store 106 :=
  store (coreStore (countStore coins [] G.encode (uniformSampleBitsPolynomial.eval N)
    (batchSize (uniformAccuracy N)) (uniformAccuracy N) (N+1) (2*uniformConfidence N+1+1)
    (G.1/2) [] [true] 0 0) (G.1/2) N)

lemma uniformInitial_eq (N : ℕ) (G : GraphInput) (he : G.1%2=0) (hd : G.1≤N) (coins : BitString) :
    uniformInitial N G coins=store (coreStore (countStore coins []
      (stateBytes (b:=N) ⟨G.1/2,some ⟨evenMatrix G he,even_bound N G he hd⟩⟩)
      (uniformSampleBitsPolynomial.eval N) (batchSize (uniformAccuracy N)) (uniformAccuracy N)
      (N+1) (2*uniformConfidence N+1+1) (G.1/2) [] [true] 0 0) (G.1/2) N) := by
  simp only [stateBytes_active,evenMatrix_input]
  rfl

 theorem core_uniform_executes (g : BitString → ℕ) (N H : ℕ) (G : GraphInput)
    (he : G.1%2=0) (hd : G.1≤N) (coins : BitString)
    (hcoins : randomBitsPolynomial.eval N≤coins.length)
    (hs : ∀i,(uniformInitial N G coins i).length≤H) :
    ∃t,core.Executes g (uniformInitial N G coins)
      (Function.update (fun _ : Fin 107 => []) 0 (estimate N G he hd coins)) t ∧
      t≤uniformCountTime.eval N+finishTime.eval (H+uniformCountTime.eval N)+2 := by
  let m := uniformSampleBitsPolynomial.eval N
  let T := uniformAccuracy N
  let h := uniformConfidence N
  let need := countingBits m T h (G.1/2)
  let r := tapeOfList need coins
  have hdepth := half_vertices_le G.1 N hd
  have hneed : need≤coins.length := (countingBits_polynomial_bound N (G.1/2) hdepth).trans hcoins
  have hreconstruct : List.ofFn r++coins.drop need=coins := tapeOfList_append_drop need coins hneed
  obtain ⟨t,ht,hb⟩ := core_coins g N m T h (G.1/2) N H (evenMatrix G he) (even_bound N G he hd) r (coins.drop need)
    (by rw [hreconstruct,←uniformInitial_eq N G he hd];exact hs)
  rw [hreconstruct,←uniformInitial_eq N G he hd] at ht
  have hc := uniformCountTime_bound N (G.1/2) hdepth
  have hm := polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hc H)
  refine ⟨t,ht,?_⟩
  dsimp only [m,T,h] at hb
  dsimp only at hm
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
