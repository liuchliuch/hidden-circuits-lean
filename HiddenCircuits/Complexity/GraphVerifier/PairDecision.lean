import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision
import HiddenCircuits.Complexity.GraphVerifier.PairScanSemantics

/-! The actual fixed-size finite truth-table program used in every graph-pair check. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def decisionInputs : List (Fin 7) := [0,1,2,3,4,5]
def pairDecisionFunction : List Bool → Bool
  | [f,b,l,r,d,a] => pairDecision f b l r d a
  | _ => false

noncomputable def pairDecisionBlock : OracleBlock 6 := decision 6 decisionInputs pairDecisionFunction

def pairDecisionBits (f b l r d a : Bool) : Fin 7 → Bool := ![f,b,l,r,d,a,false]
def pairDecisionStore (f b l r d a : Bool) : Store 6 := ![[f],[b],[l],[r],[d],[a],[]]

/-- Every local edge check executes a real finite program in exactly sixteen primitive steps. -/
theorem pairDecision_executes (g : BitString → ℕ) (f b l r d a : Bool) :
    pairDecisionBlock.Executes g (pairDecisionStore f b l r d a)
      (Function.update (fun _ : Fin 7 => ([]:BitString)) 6 [pairDecision f b l r d a]) 16 := by
  have h := decision_executes (6:Fin 7) decisionInputs (by decide +kernel) (by decide +kernel)
    pairDecisionFunction (pairDecisionBits f b l r d a) g (pairDecisionStore f b l r d a)
    (by intro i hi;fin_cases i <;> simp [decisionInputs,pairDecisionStore,pairDecisionBits] at *)
  have he : eraseStore decisionInputs (pairDecisionStore f b l r d a)=(fun _ : Fin 7 => ([]:BitString)) := by
    funext i
    fin_cases i <;> simp [eraseStore,decisionInputs,pairDecisionStore]
  rw [he] at h
  exact h

 theorem pairDecision_queryFree : pairDecisionBlock.QueryFree := decision_queryFree _ _ _

end HiddenCircuits.Complexity.GraphVerifier.Runtime
