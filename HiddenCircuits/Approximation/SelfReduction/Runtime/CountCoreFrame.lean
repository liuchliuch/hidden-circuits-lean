import HiddenCircuits.Approximation.SelfReduction.Runtime.CountLoopFailure
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountQueryFree

/-! The outer counting core preserves the original dimension and input size
outside the actual adaptive-loop work area. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock

def coreLoopPorts : Fin 71 ↪ Fin 73 where
  toFun i := i.castAdd 2
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 73 => x.val) h)

def coreStore (loop : Store 70) (originalDepth N : ℕ) : Store 72 :=
  Fin.addCases (m:=71) (n:=2) loop
    (Fin.cases (List.replicate originalDepth true) (fun _ => List.replicate N true))

@[simp] theorem coreStore_loop (loop : Store 70) (d N : ℕ) (i : Fin 71) :
    coreStore loop d N (coreLoopPorts i)=loop i := by simp [coreStore,coreLoopPorts]
@[simp] theorem coreStore_depth (loop : Store 70) (d N : ℕ) : coreStore loop d N 71=List.replicate d true := rfl
@[simp] theorem coreStore_size (loop : Store 70) (d N : ℕ) : coreStore loop d N 72=List.replicate N true := rfl

noncomputable def coreLoop : OracleBlock 72 := rename countLoop coreLoopPorts

 theorem coreLoop_executes (g : BitString → ℕ) (s t : Store 70) (cost : ℕ)
    (h : countLoop.Executes g s t cost) (d N : ℕ) :
    coreLoop.Executes g (coreStore s d N) (coreStore t d N) cost := by
  apply rename_executes_to countLoop coreLoopPorts g h
  · funext i; simp
  · funext i; simp
  · intro j
    refine Fin.addCases (m:=71) (n:=2) (fun i => ?_) (fun i => ?_) j
    · intro hj; exact False.elim (hj i rfl)
    · intro hj; simp [coreStore]

 theorem coreLoop_queryFree : coreLoop.QueryFree := rename_queryFree _ _ countLoop_queryFree
end HiddenCircuits.Approximation.SelfReduction.Runtime
