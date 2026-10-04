import HiddenCircuits.Approximation.SelfReduction.Runtime.CountCoreFrame
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountPrimitives
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountFinish

/-! The general-graph counter extends the checked 73 logical registers with34
clean sampler scratch registers. Preparation, rejection and the entire binary
output assembler are reused as real blocks with unchanged proofs. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock

def basePorts : Fin 73 ↪ Fin 107 where
  toFun i := i.castAdd 34
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 107 => x.val) h)
def loopPorts : Fin 71 ↪ Fin 107 where
  toFun i := i.castAdd 36
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 107 => x.val) h)
def stagePorts : Fin 99 ↪ Fin 107 where
  toFun i := ⟨if i.val<65 then i.val else i.val+8,by split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun x : Fin 107 => x.val) h
    dsimp at hh
    split_ifs at hh <;> omega

def store (s : Store 72) : Store 106 := Fin.addCases (m:=73) (n:=34) s (fun _ => [])

@[simp] theorem store_low (s : Store 72) (i : Fin 73) : store s (basePorts i)=s i := by
  simp [store,basePorts]
@[simp] theorem store_high (s : Store 72) (i : Fin 34) : store s (i.natAdd 73)=[] := by simp [store]

 theorem store_rename {B : OracleBlock 72} (g : BitString → ℕ) (s t : Store 72) (cost : ℕ)
    (h : B.Executes g s t cost) : (rename B basePorts).Executes g (store s) (store t) cost := by
  apply rename_executes_to B basePorts g h
  · funext i; simp
  · funext i; simp
  · intro j
    refine Fin.addCases (m:=73) (n:=34) (fun i => ?_) (fun i => ?_) j
    · intro hj; exact False.elim (hj i rfl)
    · intro hj; simp [store]

 theorem store_rename_loop {B : OracleBlock 70} (g : BitString → ℕ) (s t : Store 70) (cost : ℕ)
    (h : B.Executes g s t cost) (d N : ℕ) :
    (rename B loopPorts).Executes g (store (coreStore s d N)) (store (coreStore t d N)) cost := by
  apply rename_executes_to B loopPorts g h
  · funext i
    change store (coreStore s d N) (basePorts (coreLoopPorts i))=s i
    simp
  · funext i
    change store (coreStore t d N) (basePorts (coreLoopPorts i))=t i
    simp
  · intro j
    refine Fin.addCases (m:=73) (n:=34) (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (m:=71) (n:=2) (fun i => ?_) (fun i => ?_) i
      · intro hj; exact False.elim (hj i rfl)
      · intro hj; simp [store,coreStore]
    · intro hj; simp [store]

noncomputable def prepare : OracleBlock 106 := rename countPrepare loopPorts
noncomputable def reject : OracleBlock 106 := rename countReject loopPorts
noncomputable def finish : OracleBlock 106 := rename countFinish basePorts

 theorem prepare_executes (g : BitString → ℕ) (coins graph : BitString) (width M T cap groups depth : ℕ)
    (out alive : BitString) (d N : ℕ) :
    prepare.Executes g (store (coreStore (countStore coins [] graph width M T cap groups depth out alive 0 0) d N))
      (store (coreStore (countStore coins (sampleInput graph T) graph width M T cap groups depth out alive 0 0) d N))
      (5*T+13*graph.length+15) :=
  store_rename_loop g _ _ _ (countPrepare_executes g coins graph width M T cap groups depth out alive) d N

 theorem reject_executes (g : BitString → ℕ) (coins context graph : BitString)
    (width M T cap groups depth idx : ℕ) (out : BitString) (d N : ℕ) :
    reject.Executes g (store (coreStore (countStore coins context graph width M T cap groups depth out [true] 0 idx) d N))
      (store (coreStore (countStore coins [] graph width M T cap groups 0 out [] 0 0) d N))
      (depth+idx+context.length+11) :=
  store_rename_loop g _ _ _ (countReject_executes g coins context graph width M T cap groups depth idx out) d N

 theorem store_clean (word : BitString) : store (Function.update (fun _ : Fin 73 => []) 0 word)=
    Function.update (fun _ : Fin 107 => []) 0 word := by
  funext i
  refine Fin.addCases (m:=73) (n:=34) (fun j => ?_) (fun j => ?_) i
  · change store (Function.update (fun _ : Fin 73 => []) 0 word) (basePorts j)=_
    rw [store_low]
    by_cases hj : j=0
    · subst j; rfl
    · have hz : basePorts j≠0 := by intro h; apply hj; exact Fin.ext (congrArg (fun x : Fin 107 => x.val) h)
      have hcast : j.castAdd 34≠(0 : Fin 107) := hz
      simp [Function.update_apply,hj,hcast]
  · rw [store_high]
    have hz : j.natAdd 73≠(0 : Fin 107) := by
      intro h
      have hh := congrArg (fun x : Fin 107 => x.val) h
      simp at hh
    simp [Function.update_of_ne hz]

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
