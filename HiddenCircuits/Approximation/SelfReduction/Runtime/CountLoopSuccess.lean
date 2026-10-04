import HiddenCircuits.Approximation.SelfReduction.Runtime.CountBody
import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualCounting

/-! The successful branch of the real adaptive deletion loop. Every iteration
builds its context, samples, tallies, tests and emits the next endpoint graph. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

 def countingStageBytes (m T h d : ℕ) (tapes : Fin d → StageTape (CoinTape m) T h) : BitString :=
  (List.ofFn (fun i => stageBytes m T h (tapes i))).flatten

 theorem countingStageBytes_succ (m T h d : ℕ) (tapes : Fin (d+1) → StageTape (CoinTape m) T h) :
    countingStageBytes m T h (d+1) tapes=stageBytes m T h (tapes 0)++
      countingStageBytes m T h d (fun i => tapes i.succ) := by
  rw [countingStageBytes,List.ofFn_succ,List.flatten_cons]
  rfl

 theorem countLoop_success_while (g : BitString → ℕ) (b m T h d : ℕ)
    (E : MonotoneEndpoints d) (hE : d ≤ b+1) (tapes : Fin d → StageTape (CoinTape m) T h)
    (xs : List ℕ) (hx : shortCounts T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes=some xs) (rest out : BitString) :
    ∃ graph t, WhileExecution (67 : Fin 71) countBody countBody g
      (countStore (countingStageBytes m T h d tapes++rest) [] (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0)
      (countStore rest [] graph m (batchSize T) T (b+1) (2*h+1+1) 0
        ((unaryValues xs).reverse++out) [true] 0 0) t ∧
      t ≤ 1+d*(countBodyBound b m T h+2) := by
  induction d generalizing xs rest out with
  | zero =>
    have hxs : xs=[] := by simpa only [shortCounts,Option.some.injEq] using hx.symm
    subst xs
    refine ⟨stateBytes (b:=b) ⟨0,some ⟨E,hE⟩⟩,1,?_,by simp⟩
    simpa [countingStageBytes,unaryValues,encodeBitList] using
      (WhileExecution.empty (countStore rest [] (stateBytes (b:=b) ⟨0,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) 0 out [true] 0 0) (by rfl))
  | succ d ih =>
    let s : SelfReduction.EndpointResidual.State b := ⟨d+1,some ⟨E,hE⟩⟩
    let j := countChoice m T h s (tapes 0)
    let c := countValue m T h s (tapes 0)
    change (if c=0 then none else
      (shortCounts T m T h d (child s j) (fun i => tapes i.succ)).map (c::·))=some xs at hx
    split_ifs at hx with hz
    obtain ⟨ys,hy,hcons⟩ := Option.map_eq_some_iff.mp hx
    subst xs
    have hc : 0 < c := Nat.pos_of_ne_zero hz
    have hp : 0 < count (child s j) := endpointStage_positive m T h s (tapes 0) hc
    have hlegal := positive_child_legal E hE j hp
    let j' : Fin (d+1) := ⟨j.val,hlegal.1⟩
    let E' := SamplerRuntime.EndpointFiber.deleteFirst E j'
    have hE' : d ≤ b+1 := by omega
    have hchild : child s j=⟨d,some ⟨E',hE'⟩⟩ := child_legal E hE j hlegal.1 hlegal.2
    rw [hchild] at hy
    let tail := countingStageBytes m T h d (fun i => tapes i.succ)++rest
    let out' := (true::pairBits (List.replicate c true) []).reverse++out
    obtain ⟨graph,tt,ht,htt⟩ := ih E' hE' (fun i => tapes i.succ) ys hy rest out'
    obtain ⟨tb,hb,hbt⟩ := countBody_positive g E hE m T h (tapes 0) tail out hc
    change countBody.Executes g _ (countStore tail [] (stateBytes (child s j)) m (batchSize T) T (b+1)
      (2*h+1+1) d out' [true] 0 0) tb at hb
    rw [hchild] at hb
    have hpop : Function.update
        (countStore (countingStageBytes m T h (d+1) tapes++rest) [] (stateBytes s)
          m (batchSize T) T (b+1) (2*h+1+1) (d+1) out [true] 0 0)
        (67 : Fin 71) (List.replicate d true)=
        countStore (stageBytes m T h (tapes 0)++tail) [] (stateBytes s)
          m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0 := by
      rw [countingStageBytes_succ,List.append_assoc]
      funext i; fin_cases i <;> rfl
    have hw := WhileExecution.one
      (s := countStore (countingStageBytes m T h (d+1) tapes++rest) [] (stateBytes s)
        m (batchSize T) T (b+1) (2*h+1+1) (d+1) out [true] 0 0)
      (rest:=List.replicate d true) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨graph,2+tb+tt,?_,?_⟩
    · convert hw using 1
      · simp only [unaryValues_reverse_cons,List.append_assoc,out']
      · omega
    · nlinarith

 theorem countLoop_success (g : BitString → ℕ) (b m T h d : ℕ)
    (E : MonotoneEndpoints d) (hE : d ≤ b+1) (tapes : Fin d → StageTape (CoinTape m) T h)
    (xs : List ℕ) (hx : shortCounts T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes=some xs) (rest out : BitString) :
    ∃ graph t, countLoop.Executes g
      (countStore (countingStageBytes m T h d tapes++rest) [] (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0)
      (countStore rest [] graph m (batchSize T) T (b+1) (2*h+1+1) 0
        ((unaryValues xs).reverse++out) [true] 0 0) t ∧
      t ≤ 1+d*(countBodyBound b m T h+2) := by
  obtain ⟨graph,t,ht,hb⟩ := countLoop_success_while g b m T h d E hE tapes xs hx rest out
  exact ⟨graph,t,whilePop_executes _ _ _ _ ht,hb⟩

end HiddenCircuits.Approximation.SelfReduction.Runtime
