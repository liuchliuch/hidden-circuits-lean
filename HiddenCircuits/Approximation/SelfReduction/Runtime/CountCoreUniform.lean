import HiddenCircuits.Approximation.SelfReduction.Runtime.CountCore
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountValue

/-! The complete literal counting core on one globally padded physical tape,
using parameters depending only on the pre-random request length. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity
open GraphReduction.MonotoneEndpointEncoding
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

noncomputable def uniformInitial (N : ℕ) (E : Input) (hd : E.1 ≤ N) (coins : BitString) : Complexity.OracleBlock.Store 72 :=
  coreStore (countStore coins [] (stateBytes (b:=N) ⟨E.1,some ⟨E.2,hd.trans (Nat.le_succ N)⟩⟩)
    (uniformSampleBitsPolynomial.eval N) (batchSize (uniformAccuracy N)) (uniformAccuracy N)
    (N+1) (2*uniformConfidence N+1+1) E.1 [] [true] 0 0) E.1 N

 theorem countCore_uniform_executes (g : BitString → ℕ) (N H : ℕ) (E : Input) (hd : E.1 ≤ N)
    (coins : BitString) (hcoins : randomBitsPolynomial.eval N ≤ coins.length)
    (hs : ∀ i, (uniformInitial N E hd coins i).length ≤ H) :
    ∃ t, countCore.Executes g (uniformInitial N E hd coins)
      (Function.update (fun _ : Fin 73 => []) 0 (endpointEstimate N E hd coins)) t ∧
      t ≤ uniformCountTime.eval N+finishTime.eval (H+uniformCountTime.eval N)+2 := by
  let m := uniformSampleBitsPolynomial.eval N
  let T := uniformAccuracy N
  let h := uniformConfidence N
  let need := countingBits m T h E.1
  let r := tapeOfList need coins
  have hneed : need ≤ coins.length := (countingBits_polynomial_bound N E.1 hd).trans hcoins
  have hreconstruct : List.ofFn r++coins.drop need=coins := tapeOfList_append_drop need coins hneed
  obtain ⟨t,ht,hb⟩ := countCore_coins g N m T h E.1 N H E.2 (hd.trans (Nat.le_succ N)) r (coins.drop need)
    (by rw [hreconstruct]; exact hs)
  rw [hreconstruct] at ht
  have hc := uniformCountTime_bound N E.1 hd
  have hm := polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hc H)
  refine ⟨t,ht,?_⟩
  change t ≤ uniformCountTime.eval N+finishTime.eval (H+uniformCountTime.eval N)+2
  dsimp only [m,T,h] at hb
  dsimp only at hm
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
