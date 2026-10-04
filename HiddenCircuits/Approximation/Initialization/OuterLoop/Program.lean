import HiddenCircuits.Approximation.Initialization.OuterLoop.Data
import HiddenCircuits.Approximation.Initialization.Search.Stage.Frame

/-! The literal bounded outer extraction loop. A failed stage
physically empties the clock; successful stages continue with the next pair. -/
namespace HiddenCircuits.Approximation.Initialization.OuterLoop
open Complexity Complexity.OracleBlock SamplerRuntime
set_option maxHeartbeats 2000000

def stagePorts : Fin 51 ↪ Fin 52 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin 52 => q.val) h)
noncomputable def stage : OracleBlock 51 := Search.Stage.on stagePorts
noncomputable def afterStage : OracleBlock 51 := branchPop 7 (clear 51) (clear 51) skip
noncomputable def body : OracleBlock 51 := seq stage afterStage
noncomputable def loop : OracleBlock 51 := whilePop 51 body body

lemma stage_executes (g : BitString → ℕ) (N : ℕ) (payload mask source : BitString)
    (B : ℕ) (data : BitString) (L fuel : ℕ) (mask' source' data' ok : BitString) (t : ℕ)
    (ht : Search.Stage.program.Executes g (Search.Stage.state N payload mask source B data L [])
      (Search.Stage.state N payload mask' source' B data' L ok) t) :
    stage.Executes g (state N payload mask source B data L fuel [])
      (state N payload mask' source' B data' L fuel ok) t := by
  apply rename_executes_to Search.Stage.program stagePorts g ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hh : i.val=51 := by
      by_contra hh
      have hv : i.val<51 := by omega
      exact hi ⟨i.val,hv⟩ (Fin.ext rfl)
    have he : i=(51:Fin 52) := Fin.ext hh
    subst i;rfl

lemma afterStage_true (g : BitString → ℕ) (N : ℕ) (payload mask source : BitString)
    (B : ℕ) (data : BitString) (L fuel : ℕ) :
    afterStage.Executes g (state N payload mask source B data L fuel [true])
      (state N payload mask source B data L fuel []) 3 := by
  apply branchPop_true (7:Fin 52) _ _ _ g rfl
  convert skip_executes g (state N payload mask source B data L fuel []) using 1
  funext i;fin_cases i <;> rfl

lemma afterStage_false (g : BitString → ℕ) (N : ℕ) (payload mask source : BitString)
    (B : ℕ) (data : BitString) (L fuel : ℕ) :
    afterStage.Executes g (state N payload mask source B data L fuel [false])
      (state N payload mask source B data L 0 []) (fuel+3) := by
  have h : (clear (51:Fin 52)).Executes g (state N payload mask source B data L fuel [])
      (state N payload mask source B data L 0 []) (fuel+1) := by
    convert clear_executes g (51:Fin 52) _ using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  apply branchPop_false (7:Fin 52) _ _ _ g rfl
  convert h using 1
  funext i;fin_cases i <;> rfl

lemma pop_fuel (N : ℕ) (payload mask source : BitString) (B : ℕ) (data : BitString)
    (L fuel : ℕ) :
    Function.update (state N payload mask source B data L (fuel+1) []) (51:Fin 52) (unary fuel)=
      state N payload mask source B data L fuel [] := by
  funext i;fin_cases i <;> rfl

lemma loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _
  (seq_queryFree _ _ (Search.Stage.on_queryFree _)
    (branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _) skip_queryFree))
  (seq_queryFree _ _ (Search.Stage.on_queryFree _)
    (branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _) skip_queryFree))
end HiddenCircuits.Approximation.Initialization.OuterLoop
