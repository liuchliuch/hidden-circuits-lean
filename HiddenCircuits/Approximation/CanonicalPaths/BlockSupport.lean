import HiddenCircuits.Approximation.CanonicalPaths.BlockRotation
import Mathlib.Order.Interval.Finset.Fin

/-! Fresh support bound for neighboring primary block configurations. -/
namespace HiddenCircuits.Approximation.CanonicalPaths
variable {n : ℕ}

def endGap (b d : Fin n) : Finset (Fin n) := Finset.Ioc (min b d) (max b d)
def blockChangeSupport (a b c d : Fin n) : Finset (Fin n) := {a,c} ∪ endGap b d

theorem endGap_card_le (b d : Fin n) (hbd : b.val ≤ d.val+2) (hdb : d.val ≤ b.val+2) :
    (endGap b d).card ≤ 2 := by
  simp only [endGap,Fin.card_Ioc,Fin.coe_min,Fin.coe_max]
  omega

theorem blockChangeSupport_card (a b c d : Fin n)
    (hbd : b.val ≤ d.val+2) (hdb : d.val ≤ b.val+2) :
    (blockChangeSupport a b c d).card ≤ 4 := by
  have hp : ({a,c} : Finset (Fin n)).card ≤ 2 := by
    by_cases h : a=c <;> simp [h]
  have hg := endGap_card_le b d hbd hdb
  have hu := Finset.card_union_le ({a,c} : Finset (Fin n)) (endGap b d)
  unfold blockChangeSupport
  omega

theorem blockRotation_agree_outside [NeZero n] (a b c d : Fin n) (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a.val ≤ c.val+1) (hca : c.val ≤ a.val+1) (i : Fin n)
    (hi : i∉blockChangeSupport a b c d) : blockRotation a b i=blockRotation c d i := by
  have hh : i≠a ∧ i≠c ∧ i∉endGap b d := by
    simpa only [blockChangeSupport,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or,and_assoc] using hi
  have hgap : ¬(min b.val d.val < i.val ∧ i.val ≤ max b.val d.val) := by
    simpa only [endGap,Finset.mem_Ioc,Fin.lt_def,Fin.le_iff_val_le_val,Fin.coe_min,Fin.coe_max] using hh.2.2
  have hia : i.val≠a.val := fun h => hh.1 (Fin.ext h)
  have hic : i.val≠c.val := fun h => hh.2.1 (Fin.ext h)
  have hl : a < i ↔ c < i := by
    change a.val < i.val ↔ c.val < i.val
    omega
  have hr : i ≤ b ↔ i ≤ d := by
    change i.val ≤ b.val ↔ i.val ≤ d.val
    omega
  rw [blockRotation_apply a b i hab,blockRotation_apply c d i hcd]
  simp only [if_neg hh.1,if_neg hh.2.1,hl,hr]

end HiddenCircuits.Approximation.CanonicalPaths
