import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingBounds
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountControlAccept
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountCounting

/-! A physical empirical-factor test, with exact zero rejection and positive
factor restoration before the actual dense pair-deletion emitter. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock SelfReduction.GraphCount

 theorem decision_zero (g : BitString → ℕ) (coins context graph : BitString)
    (width M T cap groups depth idx : ℕ) (out : BitString) (d N : ℕ) :
    decision.Executes g (store (coreStore (countStore coins context graph width M T cap groups depth out [true] 0 idx) d N))
      (store (coreStore (countStore coins [] graph width M T cap groups 0 out [] 0 0) d N))
      (depth+idx+context.length+13) := by
  apply branchPop_empty _ _ _ _ g rfl
  exact reject_executes g coins context graph width M T cap groups depth idx out d N

 theorem decision_positive (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph (n+1)) (j : Fin (n+1))
    (coins context : BitString) (width M T cap groups depth c originalDepth N : ℕ)
    (hc : 0<c) (out : BitString) :
    ∃t,decision.Executes g
      (store (coreStore (countStore coins context (GraphInput.encode ⟨n+1,G⟩) width M T cap groups depth out [true] c j.val) originalDepth N))
      (store (coreStore (countStore coins [] (GraphResidual.output G j) width M T cap groups depth
        ((true::pairBits (List.replicate c true) []).reverse++out) [true] 0 0) originalDepth N)) t ∧
      t≤GraphResidual.timeBound (n+1)+9*c+j.val+context.length+20 := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
  obtain ⟨t,ht,hb⟩ := accept_executes g G j coins context width M T cap groups depth c originalDepth N out
  have hpop : Function.update
      (store (coreStore (countStore coins context (GraphInput.encode ⟨n+1,G⟩) width M T cap groups depth out [true] (c+1) j.val) originalDepth N))
      (7 : Fin 107) (List.replicate c true)=
      store (coreStore (countStore coins context (GraphInput.encode ⟨n+1,G⟩) width M T cap groups depth out [true] c j.val) originalDepth N) := by
    funext i; fin_cases i <;> rfl
  refine ⟨t+2,?_,by omega⟩
  apply branchPop_true _ _ _ _ g (rest:=List.replicate c true) (by rfl)
  rw [hpop]
  exact ht

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
