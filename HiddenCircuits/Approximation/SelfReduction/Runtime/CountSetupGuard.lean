import HiddenCircuits.Complexity.GraphVerifier.LengthAtLeast

/-! A total real length guard. The original random tape survives; both copied
comparison clocks are consumed and cleaned even on malformed/short tapes. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
open Complexity OracleBlock GraphVerifier.Runtime
set_option maxHeartbeats 800000

def guardStore (coins budget copied work flag : BitString) : Store 4 := fun i =>
  if i.val=0 then coins else if i.val=1 then budget else if i.val=2 then copied
  else if i.val=3 then work else flag

def guardPorts : Fin 3 ↪ Fin 5 where
  toFun i := ![2,1,4] i
  inj' := by decide +kernel
noncomputable def tapeGuard : OracleBlock 4 := seq (copyOn 0 2 3 (by decide) (by decide) (by decide))
  (seq (rename lengthAtLeastBlock guardPorts) (seq (clear 1) (clear 2)))
lemma tapeGuard_executes (g : BitString → ℕ) (coins budget : BitString) :
    ∃c,tapeGuard.Executes g (guardStore coins budget [] [] [])
      (guardStore coins [] [] [] [decide (budget.length≤coins.length)]) c ∧
      c≤30*(coins.length+budget.length+1) := by
  have hcopy : (copyOn (0:Fin 5) 2 3 (by decide) (by decide) (by decide)).Executes g
      (guardStore coins budget [] [] []) (guardStore coins budget coins [] []) (5*coins.length+2) := by
    convert copyOn_executes g (0:Fin 5) 2 3 (by decide) (by decide) (by decide)
      (guardStore coins budget [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [guardStore]
  obtain ⟨a,b,c,hc,hb⟩ := lengthAtLeast_executes g coins budget []
  have hs : ∀j,(lengthAtLeastStore coins budget [] j).length≤coins.length+budget.length := by
    intro j;fin_cases j
    · change coins.length≤coins.length+budget.length;omega
    · change budget.length≤coins.length+budget.length;omega
    · change 0≤coins.length+budget.length;omega
  have ha := hc.stack_bound hs (0:Fin 3)
  have hbb := hc.stack_bound hs (1:Fin 3)
  change a.length≤coins.length+budget.length+c at ha
  change b.length≤coins.length+budget.length+c at hbb
  let s := guardStore coins b a [] [decide (budget.length≤coins.length)]
  let t := guardStore coins [] a [] [decide (budget.length≤coins.length)]
  have hcomp : (rename lengthAtLeastBlock guardPorts).Executes g (guardStore coins budget coins [] []) s c := by
    apply rename_executes_to _ _ g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim
  have h₁ : (clear (1:Fin 5)).Executes g s t (b.length+1) := by
    convert clear_executes g (1:Fin 5) s using 1
    funext i;fin_cases i <;> rfl
  have h₂ : (clear (2:Fin 5)).Executes g t (guardStore coins [] [] [] [decide (budget.length≤coins.length)]) (a.length+1) := by
    convert clear_executes g (2:Fin 5) t using 1
    funext i;fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g hcopy (seq_executes _ _ g hcomp (seq_executes _ _ g h₁ h₂)),?_⟩
  have hm := Nat.min_le_left coins.length budget.length
  omega
lemma tapeGuard_queryFree : tapeGuard.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ lengthAtLeast_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))
end HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
