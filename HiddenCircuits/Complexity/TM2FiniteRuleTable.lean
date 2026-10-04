import HiddenCircuits.Complexity.TM2DirectPorts

/-! Finite, verifier-constant local-rule tables for the uniform emitter.
For a stack cell, only capped distances from the two ends are needed; arbitrary
height or position never indexes an unbounded transition table. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding
attribute [local instance] Classical.propDecidable

lemma cap_sum_succ (K j r : ℕ) :
    min (j+r+1) (2*K) = min (min j (2*K)+min r (2*K)+1) (2*K) := by omega

lemma cap_lt_iff {K j a : ℕ} (ha : a ≤ K) : j < a ↔ min j (2*K) < a := by omega

lemma cap_eq_of_lt {K j a : ℕ} (ha : a ≤ K) (hj : j < a) : min j (2*K) = j := by omega

lemma cap_shift_lt_iff {K j r a b : ℕ} (ha : a ≤ K) (hb : b ≤ K) :
    j-a+b < j+r+1 ↔ min j (2*K)-a+b < min j (2*K)+min r (2*K)+1 := by omega

noncomputable def cappedPosition (M : Turing.FinTM2) (j : ℕ) : Fin (2*inspectionConstant M+1) :=
  ⟨min j (2*inspectionConstant M),by omega⟩

lemma portComputedControl_cap (M : Turing.FinTM2) (height : ℕ) (a : Port M → Bool) :
    portComputedControl M height a = portComputedControl M (min height (2*inspectionConstant M)) a := by
  unfold portComputedControl
  rw [portSnapshot_cap M height a]

lemma effects_height_equiv (M : Turing.FinTM2) (H H' : ℕ) (a : Port M → Bool)
    (h : min H (2*inspectionConstant M) = min H' (2*inspectionConstant M)) :
    portEffects M H a = portEffects M H' a := by
  calc
    portEffects M H a = portEffects M (min H (2*inspectionConstant M)) a := portEffects_cap M H a
    _ = portEffects M (min H' (2*inspectionConstant M)) a := congrArg (fun n => portEffects M n a) h
    _ = portEffects M H' a := (portEffects_cap M H' a).symm

/-- A finite control-cell truth table: all its argument types depend only on M. -/
noncomputable def controlRuleTable (M : Turing.FinTM2) (H : Fin (2*inspectionConstant M+1))
    (q : Control M) (a : Port M → Bool) : Bool :=
  decide (portComputedControl M H.val a = q)

/-- A finite stack-cell truth table, indexed by its constant symbol identity,
local Boolean pattern, and capped left/right distances. -/
noncomputable def stackRuleTable (M : Turing.FinTM2) (j r : Fin (2*inspectionConstant M+1))
    (k : M.K) (symbol : Option (Symbol M k)) (a : Port M → Bool) : Bool :=
  directRule M (j.val+r.val+1) (Sum.inr ⟨k,(⟨j.val,by omega⟩,symbol)⟩) a

/-- The control table exactly evaluates the actual local transition. -/
theorem controlRuleTable_correct (M : Turing.FinTM2) (H : ℕ) (q : Control M) (a : Port M → Bool) :
    directRule M H (Sum.inl q) a = controlRuleTable M (cappedPosition M H) q a := by
  simp only [directRule,controlRuleTable,cappedPosition,portComputedControl_cap M H a]

/-- Capped boundary classes suffice for the exact stack-cell transition.
No uniform runtime assertion is hidden in the finite table definition. -/
theorem stackRuleTable_correct (M : Turing.FinTM2) (H : ℕ) (k : M.K) (i : Fin H)
    (symbol : Option (Symbol M k)) (a : Port M → Bool) :
    directRule M H (Sum.inr ⟨k,(i,symbol)⟩) a =
      stackRuleTable M (cappedPosition M i.val) (cappedPosition M (H-i.val-1)) k symbol a := by
  classical
  let K := inspectionConstant M
  let j := i.val
  let r := H-i.val-1
  let j' := min j (2*K)
  let r' := min r (2*K)
  let H' := j'+r'+1
  have hH : H = j+r+1 := by have := i.isLt;dsimp [j,r];omega
  have hc : min H (2*K) = min H' (2*K) := by
    rw [hH];exact cap_sum_succ K j r
  have he := effects_height_equiv M H H' a hc
  have hcost := portEffects_cost M H' a k
  have hlen : (portEffects M H' a k).inserted.length ≤ K := by
    dsimp [StackEffect.cost] at hcost;omega
  have hrem : (portEffects M H' a k).removed ≤ K := by
    dsimp [StackEffect.cost] at hcost;omega
  change directRule M H (Sum.inr ⟨k,(i,symbol)⟩) a =
    directRule M H' (Sum.inr ⟨k,(⟨j',by dsimp [H'];omega⟩,symbol)⟩) a
  simp only [directRule,he]
  have htest : j < (portEffects M H' a k).inserted.length ↔ j' < (portEffects M H' a k).inserted.length :=
    cap_lt_iff hlen
  by_cases hi : j < (portEffects M H' a k).inserted.length
  · have hje : j'=j := cap_eq_of_lt hlen hi
    simp only [show i.val=j from rfl,if_pos hi,if_pos (htest.mp hi),hje]
  · have hi' := mt htest.mpr hi
    simp only [show i.val=j from rfl,if_neg hi,if_neg hi']
    have hslot : j-(portEffects M H' a k).inserted.length+(portEffects M H' a k).removed < H ↔
        j'-(portEffects M H' a k).inserted.length+(portEffects M H' a k).removed < H' := by
      rw [hH];exact cap_shift_lt_iff hlen hrem
    simp only [portSlot,effectPort,portPosition,he,hslot]

end HiddenCircuits.Complexity.TM2BooleanEncoding
