import HiddenCircuits.Small.Gate8States

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def gate8PermMaps : Fin 24 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0], ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]
def gate8PermInvMaps : Fin 24 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 3, 1, 2], ![0, 2, 3, 1], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2], ![2, 0, 1, 3], ![3, 0, 1, 2], ![2, 0, 3, 1], ![3, 0, 2, 1], ![1, 2, 0, 3], ![1, 3, 0, 2], ![2, 1, 0, 3], ![3, 1, 0, 2], ![2, 3, 0, 1], ![3, 2, 0, 1], ![1, 2, 3, 0], ![1, 3, 2, 0], ![2, 1, 3, 0], ![3, 1, 2, 0], ![2, 3, 1, 0], ![3, 2, 1, 0]]
theorem gate8Perm_left : ∀ a b, gate8PermInvMaps a (gate8PermMaps a b) = b := by decide +kernel
theorem gate8Perm_right : ∀ a b, gate8PermMaps a (gate8PermInvMaps a b) = b := by decide +kernel
def gate8Perms (a : Fin 24) : Equiv.Perm (Fin 4) := ⟨gate8PermMaps a, gate8PermInvMaps a, gate8Perm_left a, gate8Perm_right a⟩
theorem gate8Perms_injective : Function.Injective gate8Perms := by decide +kernel
theorem gate8Perms_complete : finitePerms 4 = Finset.univ.image gate8Perms := by decide +kernel
theorem gate8_permanent_explicit (M : Matrix (Fin 4) (Fin 4) ℚ) :
  M.permanent = ∑ a : Fin 24, ∏ j : Fin 4, M (gate8PermMaps a j) j := by
  rw [permanent_eq_explicit, gate8Perms_complete]
  exact Finset.sum_image (fun a _ b _ h => gate8Perms_injective h)

end HiddenCircuits.Small
