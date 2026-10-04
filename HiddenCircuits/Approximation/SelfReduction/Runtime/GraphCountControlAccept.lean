import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountControlFrame
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualProgram

/-! Observed-positive control for the general graph counter. The full dense
pair-deletion emitter is called as a real block; every nonoutput port is framed. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock

def residualPorts : Fin 19 ↪ Fin 73 where
  toFun i := ![65,8,3,4,5,6,9,10,11,12,13,14,15,16,17,18,19,20,21] i
  inj' := by decide +kernel
noncomputable def acceptSmall : OracleBlock 72 := seq (push 7 true) (seq (emitUnaryReversed 7 68)
  (seq (GraphResidual.programOn residualPorts) (seq (clear 8) (clear 1))))
noncomputable def accept : OracleBlock 106 := rename acceptSmall basePorts
noncomputable def decision : OracleBlock 106 := branchPop 7 reject accept accept

 theorem acceptSmall_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph (n+1)) (j : Fin (n+1))
    (coins context : BitString) (width M T cap groups depth c originalDepth N : ℕ) (out : BitString) :
    ∃ t, acceptSmall.Executes g
      (coreStore (countStore coins context (GraphInput.encode ⟨n+1,G⟩) width M T cap groups depth out [true] c j.val) originalDepth N)
      (coreStore (countStore coins [] (GraphResidual.output G j) width M T cap groups depth
        ((true::pairBits (List.replicate (c+1) true) []).reverse++out) [true] 0 0) originalDepth N) t ∧
      t ≤ GraphResidual.timeBound (n+1)+9*(c+1)+j.val+context.length+18 := by
  let graph := GraphInput.encode ⟨n+1,G⟩
  let graph' := GraphResidual.output G j
  let out' := (true::pairBits (List.replicate (c+1) true) []).reverse++out
  let s0 := coreStore (countStore coins context graph width M T cap groups depth out [true] c j.val) originalDepth N
  let s1 := coreStore (countStore coins context graph width M T cap groups depth out [true] (c+1) j.val) originalDepth N
  let s2 := coreStore (countStore coins context graph width M T cap groups depth out' [true] 0 j.val) originalDepth N
  let s3 := coreStore (countStore coins context graph' width M T cap groups depth out' [true] 0 j.val) originalDepth N
  let s4 := coreStore (countStore coins context graph' width M T cap groups depth out' [true] 0 0) originalDepth N
  let sf := coreStore (countStore coins [] graph' width M T cap groups depth out' [true] 0 0) originalDepth N
  have h1 : (push (7 : Fin 73) true).Executes g s0 s1 1 := by
    convert push_executes g (7 : Fin 73) true s0 using 1
    funext i; fin_cases i <;> first | rfl | (change List.replicate (c+1) true=true::List.replicate c true; simp [List.replicate_succ])
  have h2 : (emitUnaryReversed (7 : Fin 73) 68).Executes g s1 s2 (9*(c+1)+7) := by
    have he := emitUnaryReversed_executes g (7 : Fin 73) 68 (by decide) s1
    rw [show s1 7=List.replicate (c+1) true from rfl,show s1 68=out from rfl,List.length_replicate] at he
    convert he using 1
    funext i; fin_cases i <;> rfl
  obtain ⟨tr,hr,hbr⟩ := GraphResidual.programOn_executes residualPorts g s2 G j (by funext i; fin_cases i <;> rfl)
  have h3 : (GraphResidual.programOn residualPorts).Executes g s2 s3 tr := by
    convert hr using 1
    funext i; fin_cases i <;> rfl
  have h4 : (clear (8 : Fin 73)).Executes g s3 s4 (j.val+1) := by
    convert clear_executes g (8 : Fin 73) s3 using 1
    · funext i; fin_cases i <;> rfl
    · change j.val+1=(List.replicate j.val true).length+1
      simp
  have h5 : (clear (1 : Fin 73)).Executes g s4 sf (context.length+1) := by
    convert clear_executes g (1 : Fin 73) s4 using 1
    funext i; fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  omega

 theorem accept_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph (n+1)) (j : Fin (n+1))
    (coins context : BitString) (width M T cap groups depth c originalDepth N : ℕ) (out : BitString) :
    ∃ t, accept.Executes g
      (store (coreStore (countStore coins context (GraphInput.encode ⟨n+1,G⟩) width M T cap groups depth out [true] c j.val) originalDepth N))
      (store (coreStore (countStore coins [] (GraphResidual.output G j) width M T cap groups depth
        ((true::pairBits (List.replicate (c+1) true) []).reverse++out) [true] 0 0) originalDepth N)) t ∧
      t ≤ GraphResidual.timeBound (n+1)+9*(c+1)+j.val+context.length+18 := by
  obtain ⟨t,ht,hb⟩ := acceptSmall_executes g G j coins context width M T cap groups depth c originalDepth N out
  exact ⟨t,store_rename g _ _ _ ht,hb⟩

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
