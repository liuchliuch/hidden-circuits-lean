import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingBody
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountLoopSuccess

/-! The successful branch of the real adaptive deletion loop. Every iteration
builds its context, samples, tallies, tests and emits the next endpoint graph. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock
open HiddenCircuits.Approximation.SelfReduction.GraphCount

def machineStore (originalDepth N : ℕ) (coins context graph : BitString) (width M T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) : Store 106 :=
  store (coreStore (countStore coins context graph width M T cap groups depth out alive value idx) originalDepth N)

 theorem loop_success_while (g : BitString → ℕ) (b m T h d originalDepth N : ℕ)
    (E : MatrixGraph (2*d)) (hE : 2*d ≤ b+1) (tapes : Fin d → StageTape (CoinTape m) T h)
    (xs : List ℕ) (hx : shortCounts T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes=some xs) (rest out : BitString) :
    ∃ graph t, WhileExecution (67 : Fin 107) body body g
      (machineStore originalDepth N (countingStageBytes m T h d tapes++rest) [] (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0)
      (machineStore originalDepth N rest [] graph m (batchSize T) T (b+1) (2*h+1+1) 0
        ((unaryValues xs).reverse++out) [true] 0 0) t ∧
      t ≤ 1+d*(bodyBound b m T h+2) := by
  induction d generalizing xs rest out with
  | zero =>
    have hxs : xs=[] := by simpa only [shortCounts,Option.some.injEq] using hx.symm
    subst xs
    refine ⟨stateBytes (b:=b) ⟨0,some ⟨E,hE⟩⟩,1,?_,by simp⟩
    simpa [countingStageBytes,unaryValues,encodeBitList] using
      (WhileExecution.empty (machineStore originalDepth N rest [] (stateBytes (b:=b) ⟨0,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) 0 out [true] 0 0) (by rfl))
  | succ d ih =>
    let s : SelfReduction.GraphCount.State b := ⟨d+1,some ⟨E,hE⟩⟩
    let j := choice m T h s (tapes 0)
    let c := value m T h s (tapes 0)
    change (if c=0 then none else
      (shortCounts T m T h d (child s j) (fun i => tapes i.succ)).map (c::·))=some xs at hx
    split_ifs at hx with hz
    obtain ⟨ys,hy,hcons⟩ := Option.map_eq_some_iff.mp hx
    subst xs
    have hc : 0 < c := Nat.pos_of_ne_zero hz
    have hp : 0 < count (child s j) := chosenCount_child_positive T m T h s (tapes 0) hc
    have hlegal := positive_child_legal E hE j hp
    let j' : Fin (2*(d+1)) := ⟨j.val,hlegal.1⟩
    let E' := GraphResidual.evenGraph E j' hlegal.2.ne.symm
    have hE' : 2*d ≤ b+1 := by omega
    have hchild : child s j=⟨d,some ⟨E',hE'⟩⟩ := child_legal E hE j hlegal.1 hlegal.2
    rw [hchild] at hy
    let tail := countingStageBytes m T h d (fun i => tapes i.succ)++rest
    let out' := (true::pairBits (List.replicate c true) []).reverse++out
    obtain ⟨graph,tt,ht,htt⟩ := ih E' hE' (fun i => tapes i.succ) ys hy rest out'
    obtain ⟨tb,hb,hbt⟩ := body_positive g E hE m T h originalDepth N (tapes 0) tail out hc
    change body.Executes g _ (machineStore originalDepth N tail [] (stateBytes (child s j)) m (batchSize T) T (b+1)
      (2*h+1+1) d out' [true] 0 0) tb at hb
    rw [hchild] at hb
    have hpop : Function.update
        (machineStore originalDepth N (countingStageBytes m T h (d+1) tapes++rest) [] (stateBytes s)
          m (batchSize T) T (b+1) (2*h+1+1) (d+1) out [true] 0 0)
        (67 : Fin 107) (List.replicate d true)=
        machineStore originalDepth N (stageBytes m T h (tapes 0)++tail) [] (stateBytes s)
          m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0 := by
      rw [countingStageBytes_succ,List.append_assoc]
      funext i; fin_cases i <;> rfl
    have hw := WhileExecution.one
      (s := machineStore originalDepth N (countingStageBytes m T h (d+1) tapes++rest) [] (stateBytes s)
        m (batchSize T) T (b+1) (2*h+1+1) (d+1) out [true] 0 0)
      (rest:=List.replicate d true) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨graph,2+tb+tt,?_,?_⟩
    · convert hw using 1
      · simp only [unaryValues_reverse_cons,List.append_assoc,out']
      · omega
    · nlinarith

 theorem loop_success (g : BitString → ℕ) (b m T h d originalDepth N : ℕ)
    (E : MatrixGraph (2*d)) (hE : 2*d ≤ b+1) (tapes : Fin d → StageTape (CoinTape m) T h)
    (xs : List ℕ) (hx : shortCounts T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes=some xs) (rest out : BitString) :
    ∃ graph t, loop.Executes g
      (machineStore originalDepth N (countingStageBytes m T h d tapes++rest) [] (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0)
      (machineStore originalDepth N rest [] graph m (batchSize T) T (b+1) (2*h+1+1) 0
        ((unaryValues xs).reverse++out) [true] 0 0) t ∧
      t ≤ 1+d*(bodyBound b m T h+2) := by
  obtain ⟨graph,t,ht,hb⟩ := loop_success_while g b m T h d originalDepth N E hE tapes xs hx rest out
  exact ⟨graph,t,whilePop_executes _ _ _ _ ht,hb⟩

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
