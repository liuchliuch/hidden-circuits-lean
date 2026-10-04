import HiddenCircuits.Approximation.SelfReduction.Runtime.CountFinish
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountPolynomial
import HiddenCircuits.Approximation.SelfReduction.Runtime.ShortCountsBounds
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountCoins
import HiddenCircuits.Approximation.SelfReduction.Runtime.ListTape

/-! Complete actual counting core: adaptive sampler-based deletion, early zero,
observed-factor conversion, binary numerator/denominator and clean ratio output. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

noncomputable def countCore : OracleBlock 72 := seq coreLoop countFinish

 theorem countCore_executes (g : BitString → ℕ) (b m T h d N H : ℕ)
    (E : MonotoneEndpoints d) (hE : d ≤ b+1) (tapes : Fin d → StageTape (CoinTape m) T h) (rest : BitString)
    (hs : ∀ i, (coreStore (countStore (countingStageBytes m T h d tapes++rest) []
      (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N i).length ≤ H) :
    ∃ t, countCore.Executes g
      (coreStore (countStore (countingStageBytes m T h d tapes++rest) []
        (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N)
      (Function.update (fun _ : Fin 73 => []) 0 (shortOutput T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes)) t ∧
      t ≤ (1+d*(countBodyBound b m T h+2))+
        finishTime.eval (H+(1+d*(countBodyBound b m T h+2)))+2 := by
  let initial := coreStore (countStore (countingStageBytes m T h d tapes++rest) []
    (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N
  cases hx : shortCounts T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes with
  | none =>
    obtain ⟨coins,graph,out,tl,hl,hbl⟩ := countLoop_failure g b m T h d E hE tapes hx rest []
    have hlift : coreLoop.Executes g initial (finishSource coins graph m (batchSize T) T (b+1) (2*h+1+1) out [] d N) tl := by
      rw [finishSource_eq]
      exact coreLoop_executes g _ _ _ hl d N
    obtain ⟨tf,hf,hbf⟩ := countFinish_zero g coins graph m (batchSize T) T (b+1) (2*h+1+1) out d N (H+tl)
      (hlift.stack_bound hs)
    have hmono := polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hbl H)
    dsimp only at hmono
    refine ⟨tl+tf+2,?_,by omega⟩
    simpa only [shortOutput,Option.isNone_some,Bool.false_eq_true,if_false,hx] using seq_executes _ _ g hlift hf
  | some xs =>
    obtain ⟨graph,tl,hl,hbl⟩ := countLoop_success g b m T h d E hE tapes xs hx rest []
    have hlift : coreLoop.Executes g initial
        (finishSource rest graph m (batchSize T) T (b+1) (2*h+1+1) (unaryValues xs).reverse [true] d N) tl := by
      rw [finishSource_eq]
      exact coreLoop_executes g _ _ _ (by simpa only [List.append_nil] using hl) d N
    obtain ⟨hlen,hpos⟩ := shortCounts_bounds T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes xs hx
    obtain ⟨tf,hf,hbf⟩ := countFinish_success g rest graph m (batchSize T) T (b+1) (2*h+1+1) d N (H+tl)
      xs hlen (fun c hc => (hpos c hc).1) (hlift.stack_bound hs)
    have hmono := polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hbl H)
    dsimp only at hmono
    refine ⟨tl+tf+2,?_,by omega⟩
    simpa only [shortOutput,Option.isNone_some,Bool.false_eq_true,if_false,hx] using seq_executes _ _ g hlift hf

 theorem countCore_coins (g : BitString → ℕ) (b m T h d N H : ℕ)
    (E : MonotoneEndpoints d) (hE : d ≤ b+1) (r : CoinTape (countingBits m T h d)) (rest : BitString)
    (hs : ∀ i, (coreStore (countStore (List.ofFn r++rest) []
      (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N i).length ≤ H) :
    ∃ t, countCore.Executes g
      (coreStore (countStore (List.ofFn r++rest) [] (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N)
      (Function.update (fun _ : Fin 73 => []) 0
        (shortOutput T m T h d ⟨d,some ⟨E,hE⟩⟩ (countingTapes m T h d r))) t ∧
      t ≤ (1+d*(countBodyBound b m T h+2))+
        finishTime.eval (H+(1+d*(countBodyBound b m T h+2)))+2 := by
  simpa only [countingStageBytes_countingTapes] using countCore_executes g b m T h d N H E hE
    (countingTapes m T h d r) rest (by simpa only [countingStageBytes_countingTapes] using hs)

 theorem countCore_queryFree : countCore.QueryFree := seq_queryFree _ _ coreLoop_queryFree countFinish_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime
