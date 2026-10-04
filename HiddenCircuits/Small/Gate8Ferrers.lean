import HiddenCircuits.Small.Gate8NatCompound

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def gate8SuffixPermanent (x : Fin 4 → Fin 5) : ℕ :=
  ∑ σ : Fin 24, ∏ j : Fin 4,
    if (x (gate8PermMaps σ j)).val ≤ j.val then 1 else 0

def gate8FastPermanent (x : Fin 4 → Fin 5) : ℕ :=
  ∏ j : Fin 4, (((List.finRange 4).filter (fun i => (x i).val ≤ j.val)).length - j.val)

theorem gate8FerrersLiteral : ∀ a b c d : Fin 5,
    gate8SuffixPermanent ![a,b,c,d] = gate8FastPermanent ![a,b,c,d] := by
  decide +kernel

theorem gate8Ferrers (x : Fin 4 → Fin 5) :
    gate8SuffixPermanent x = gate8FastPermanent x := by
  have h : x = ![x 0,x 1,x 2,x 3] := by ext i; fin_cases i <;> rfl
  rw [h]
  exact gate8FerrersLiteral _ _ _ _

end HiddenCircuits.Small
