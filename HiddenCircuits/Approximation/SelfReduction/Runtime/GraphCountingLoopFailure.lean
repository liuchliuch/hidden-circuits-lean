import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingLoopSuccess

/-! Failure is a real early halt, never a call on a rejected residual. A partial
count stream and unused coins remain framed until the final zero-output cleanup. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock
open HiddenCircuits.Approximation.SelfReduction.GraphCount

 theorem loop_failure_while (g : BitString → ℕ) (b m T h d originalDepth N : ℕ)
    (E : MatrixGraph (2*d)) (hE : 2*d ≤ b+1) (tapes : Fin d → StageTape (CoinTape m) T h)
    (hx : shortCounts T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes=none) (rest out : BitString) :
    ∃ coins graph out' t, WhileExecution (67 : Fin 107) body body g
      (machineStore originalDepth N (countingStageBytes m T h d tapes++rest) [] (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0)
      (machineStore originalDepth N coins [] graph m (batchSize T) T (b+1) (2*h+1+1) 0 out' [] 0 0) t ∧
      t ≤ 1+d*(bodyBound b m T h+2) := by
  induction d generalizing rest out with
  | zero => simp [shortCounts] at hx
  | succ d ih =>
    let s : SelfReduction.GraphCount.State b := ⟨d+1,some ⟨E,hE⟩⟩
    let j := choice m T h s (tapes 0)
    let c := value m T h s (tapes 0)
    let tail := countingStageBytes m T h d (fun i => tapes i.succ)++rest
    change (if c=0 then none else
      (shortCounts T m T h d (child s j) (fun i => tapes i.succ)).map (c::·))=none at hx
    have hpop : Function.update
        (machineStore originalDepth N (countingStageBytes m T h (d+1) tapes++rest) [] (stateBytes s)
          m (batchSize T) T (b+1) (2*h+1+1) (d+1) out [true] 0 0)
        (67 : Fin 107) (List.replicate d true)=
        machineStore originalDepth N (stageBytes m T h (tapes 0)++tail) [] (stateBytes s)
          m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0 := by
      rw [countingStageBytes_succ,List.append_assoc]
      funext i; fin_cases i <;> rfl
    by_cases hz : c=0
    · obtain ⟨tb,hb,hbt⟩ := body_zero g E hE m T h originalDepth N (tapes 0) tail out hz
      have ht : WhileExecution (67 : Fin 107) body body g
          (machineStore originalDepth N tail [] (stateBytes s) m (batchSize T) T (b+1) (2*h+1+1) 0 out [] 0 0)
          (machineStore originalDepth N tail [] (stateBytes s) m (batchSize T) T (b+1) (2*h+1+1) 0 out [] 0 0) 1 :=
        WhileExecution.empty _ (by rfl)
      have hw := WhileExecution.one
        (s := machineStore originalDepth N (countingStageBytes m T h (d+1) tapes++rest) [] (stateBytes s)
          m (batchSize T) T (b+1) (2*h+1+1) (d+1) out [true] 0 0)
        (rest:=List.replicate d true) (by rfl) (by rw [hpop]; exact hb) ht
      refine ⟨tail,stateBytes s,out,2+tb+1,?_,?_⟩
      · convert hw using 1 <;> omega
      · nlinarith
    · have hy : shortCounts T m T h d (child s j) (fun i => tapes i.succ)=none := by
        simpa only [if_neg hz,Option.map_eq_none_iff] using hx
      have hc : 0 < c := Nat.pos_of_ne_zero hz
      have hp : 0 < count (child s j) := chosenCount_child_positive T m T h s (tapes 0) hc
      have hlegal := positive_child_legal E hE j hp
      let j' : Fin (2*(d+1)) := ⟨j.val,hlegal.1⟩
      let E' := GraphResidual.evenGraph E j' hlegal.2.ne.symm
      have hE' : 2*d ≤ b+1 := by omega
      have hchild : child s j=⟨d,some ⟨E',hE'⟩⟩ := child_legal E hE j hlegal.1 hlegal.2
      rw [hchild] at hy
      let out' := (true::pairBits (List.replicate c true) []).reverse++out
      obtain ⟨coins,graph,out'',tt,ht,htt⟩ := ih E' hE' (fun i => tapes i.succ) hy rest out'
      obtain ⟨tb,hb,hbt⟩ := body_positive g E hE m T h originalDepth N (tapes 0) tail out hc
      change body.Executes g _ (machineStore originalDepth N tail [] (stateBytes (child s j)) m (batchSize T) T (b+1)
        (2*h+1+1) d out' [true] 0 0) tb at hb
      rw [hchild] at hb
      have hw := WhileExecution.one
        (s := machineStore originalDepth N (countingStageBytes m T h (d+1) tapes++rest) [] (stateBytes s)
          m (batchSize T) T (b+1) (2*h+1+1) (d+1) out [true] 0 0)
        (rest:=List.replicate d true) (by rfl) (by rw [hpop]; exact hb) ht
      refine ⟨coins,graph,out'',2+tb+tt,?_,?_⟩
      · convert hw using 1 <;> omega
      · nlinarith

 theorem loop_failure (g : BitString → ℕ) (b m T h d originalDepth N : ℕ)
    (E : MatrixGraph (2*d)) (hE : 2*d ≤ b+1) (tapes : Fin d → StageTape (CoinTape m) T h)
    (hx : shortCounts T m T h d ⟨d,some ⟨E,hE⟩⟩ tapes=none) (rest out : BitString) :
    ∃ coins graph out' t, loop.Executes g
      (machineStore originalDepth N (countingStageBytes m T h d tapes++rest) [] (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩)
        m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0)
      (machineStore originalDepth N coins [] graph m (batchSize T) T (b+1) (2*h+1+1) 0 out' [] 0 0) t ∧
      t ≤ 1+d*(bodyBound b m T h+2) := by
  obtain ⟨coins,graph,out',t,ht,hb⟩ := loop_failure_while g b m T h d originalDepth N E hE tapes hx rest out
  exact ⟨coins,graph,out',t,whilePop_executes _ _ _ _ ht,hb⟩

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
