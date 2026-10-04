import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingLoopFailure
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingQueryFree
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingStreamBounds
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountCoins
import HiddenCircuits.Approximation.SelfReduction.Runtime.ListTape

/-! Complete actual counting core: adaptive sampler-based deletion, early zero,
observed-factor conversion, binary numerator/denominator and clean ratio output. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock
open HiddenCircuits.Approximation.SelfReduction.GraphCount

noncomputable def core : OracleBlock 106 := seq loop finish

 theorem core_executes (g : BitString → ℕ) (b m T h d N H : ℕ)
    (E : MatrixGraph (2*d)) (hE : 2*d ≤ b+1) (tapes : Fin d → StageTape (CoinTape m) T h) (rest : BitString)
    (hs : ∀ i, (store (coreStore (countStore (countingStageBytes m T h d tapes++rest) []
      (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N) i).length ≤ H) :
    ∃ t, core.Executes g
      (store (coreStore (countStore (countingStageBytes m T h d tapes++rest) []
        (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N))
      (Function.update (fun _ : Fin 107 => []) 0 (shortOutput T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes)) t ∧
      t ≤ (1+d*(bodyBound b m T h+2))+
        finishTime.eval (H+(1+d*(bodyBound b m T h+2)))+2 := by
  let initial := store (coreStore (countStore (countingStageBytes m T h d tapes++rest) []
    (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N)
  cases hx : shortCounts T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes with
  | none =>
    obtain ⟨coins,graph,out,tl,hl,hbl⟩ := loop_failure g b m T h d d N E hE tapes hx rest []
    have hlift : loop.Executes g initial (store (finishSource coins graph m (batchSize T) T (b+1) (2*h+1+1) out [] d N)) tl := by
      rw [finishSource_eq]
      exact hl
    obtain ⟨tf,hf,hbf⟩ := countFinish_zero g coins graph m (batchSize T) T (b+1) (2*h+1+1) out d N (H+tl)
      (by intro i; simpa only [OracleBlock.config,store_low] using hlift.stack_bound hs (basePorts i))
    have hf := store_rename g _ _ _ hf
    rw [store_clean] at hf
    have hmono := polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hbl H)
    dsimp only at hmono
    refine ⟨tl+tf+2,?_,by omega⟩
    simpa only [shortOutput,Option.isNone_some,Bool.false_eq_true,if_false,hx] using seq_executes _ _ g hlift hf
  | some xs =>
    obtain ⟨graph,tl,hl,hbl⟩ := loop_success g b m T h d d N E hE tapes xs hx rest []
    have hlift : loop.Executes g initial
        (store (finishSource rest graph m (batchSize T) T (b+1) (2*h+1+1) (unaryValues xs).reverse [true] d N)) tl := by
      rw [finishSource_eq]
      simpa only [List.append_nil] using hl
    obtain ⟨hlen,hpos⟩ := shortCounts_bounds T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes xs hx
    obtain ⟨tf,hf,hbf⟩ := countFinish_success g rest graph m (batchSize T) T (b+1) (2*h+1+1) d N (H+tl)
      xs hlen (fun c hc => (hpos c hc).1) (by intro i; simpa only [OracleBlock.config,store_low] using hlift.stack_bound hs (basePorts i))
    have hf := store_rename g _ _ _ hf
    rw [store_clean] at hf
    have hmono := polynomial_nat_eval_mono finishTime (Nat.add_le_add_left hbl H)
    dsimp only at hmono
    refine ⟨tl+tf+2,?_,by omega⟩
    simpa only [shortOutput,Option.isNone_some,Bool.false_eq_true,if_false,hx] using seq_executes _ _ g hlift hf

 theorem core_coins (g : BitString → ℕ) (b m T h d N H : ℕ)
    (E : MatrixGraph (2*d)) (hE : 2*d ≤ b+1) (r : CoinTape (countingBits m T h d)) (rest : BitString)
    (hs : ∀ i, (store (coreStore (countStore (List.ofFn r++rest) []
      (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N) i).length ≤ H) :
    ∃ t, core.Executes g
      (store (coreStore (countStore (List.ofFn r++rest) [] (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) d [] [true] 0 0) d N))
      (Function.update (fun _ : Fin 107 => []) 0
        (shortOutput T m T h d ⟨d,some ⟨E,hE⟩⟩ (countingTapes m T h d r))) t ∧
      t ≤ (1+d*(bodyBound b m T h+2))+
        finishTime.eval (H+(1+d*(bodyBound b m T h+2)))+2 := by
  simpa only [countingStageBytes_countingTapes] using core_executes g b m T h d N H E hE
    (countingTapes m T h d r) rest (by simpa only [countingStageBytes_countingTapes] using hs)

 theorem core_queryFree : core.QueryFree := seq_queryFree _ _ loop_queryFree finish_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
