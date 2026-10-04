import HiddenCircuits.Small.Gate8R5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8B5Rows : Fin 70 → List (Fin 70 × ℚ) := ![[(0,2)],
  [(1,2)],
  [(4,-2)],
  [(2,1), (3,1)],
  [(4,2)],
  [(5,2)],
  [(8,-2)],
  [(6,1), (7,1)],
  [(8,2)],
  [(11,-2)],
  [(9,1), (10,1)],
  [(11,2)],
  [(12,1)],
  [],
  [(13,1), (14,1)],
  [(15,2)],
  [(18,-2)],
  [(16,1), (17,1)],
  [(18,2)],
  [(21,-2)],
  [(19,1), (20,1)],
  [(21,2)],
  [(22,1)],
  [],
  [(23,1), (24,1)],
  [(27,-2)],
  [(25,1), (26,1)],
  [(27,2)],
  [(28,1)],
  [],
  [(29,1), (30,1)],
  [(31,1)],
  [],
  [(32,1), (33,1)],
  [(34,1)],
  [(35,2)],
  [(38,-2)],
  [(36,1), (37,1)],
  [(38,2)],
  [(41,-2)],
  [(39,1), (40,1)],
  [(41,2)],
  [(42,1)],
  [],
  [(43,1), (44,1)],
  [(47,-2)],
  [(45,1), (46,1)],
  [(47,2)],
  [(48,1)],
  [],
  [(49,1), (50,1)],
  [(51,1)],
  [],
  [(52,1), (53,1)],
  [(54,1)],
  [(57,-2)],
  [(55,1), (56,1)],
  [(57,2)],
  [(58,1)],
  [],
  [(59,1), (60,1)],
  [(61,1)],
  [],
  [(62,1), (63,1)],
  [(64,1)],
  [(65,1)],
  [],
  [(66,1), (67,1)],
  [(68,1)],
  [(69,1)]]
def Gate8B5 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8B5Rows
theorem gate8_dualRise5_table : ∀ a b, Gate8R5 (gate8Complement b) (gate8Complement a) = Gate8B5 a b := by
  decide +kernel
theorem gate8_dualRise5 : compress gate8Enum (dualRise 8 4 5) = Gate8B5 := by
  ext a b
  change rise 8 (8-4) 5 ((gate8States b).complement) ((gate8States a).complement) = _
  rw [gate8States_complement, gate8States_complement]
  change (compress gate8Enum (rise 8 4 5)) (gate8Complement b) (gate8Complement a) = _
  rw [gate8_rise5]
  exact gate8_dualRise5_table a b

end HiddenCircuits.Small
