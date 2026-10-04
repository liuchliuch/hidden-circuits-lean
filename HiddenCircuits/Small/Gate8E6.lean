import HiddenCircuits.Small.Gate8D6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8E6Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [(3,1), (4,1)],
  [],
  [],
  [],
  [(7,1), (8,1)],
  [],
  [],
  [(10,1), (11,1)],
  [],
  [(12,1), (13,1)],
  [],
  [(14,1)],
  [],
  [],
  [(17,1), (18,1)],
  [],
  [],
  [(20,1), (21,1)],
  [],
  [(22,1), (23,1)],
  [],
  [(24,1)],
  [],
  [(26,1), (27,1)],
  [],
  [(28,1), (29,1)],
  [],
  [(30,1)],
  [(31,1), (32,1)],
  [],
  [(33,1)],
  [(34,1)],
  [],
  [],
  [(37,1), (38,1)],
  [],
  [],
  [(40,1), (41,1)],
  [],
  [(42,1), (43,1)],
  [],
  [(44,1)],
  [],
  [(46,1), (47,1)],
  [],
  [(48,1), (49,1)],
  [],
  [(50,1)],
  [(51,1), (52,1)],
  [],
  [(53,1)],
  [(54,1)],
  [],
  [(56,1), (57,1)],
  [],
  [(58,1), (59,1)],
  [],
  [(60,1)],
  [(61,1), (62,1)],
  [],
  [(63,1)],
  [(64,1)],
  [(65,1), (66,1)],
  [],
  [(67,1)],
  [(68,1)],
  [(69,1)]]
def Gate8E6 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8E6Rows
theorem gate8_dualDrop6_table : ∀ a b, Gate8D6 (gate8Complement b) (gate8Complement a) = Gate8E6 a b := by
  decide +kernel
theorem gate8_dualDrop6 : compress gate8Enum (dualDrop 8 4 6) = Gate8E6 := by
  ext a b
  change drop 8 (8-4) 6 ((gate8States b).complement) ((gate8States a).complement) = _
  rw [gate8States_complement, gate8States_complement]
  change (compress gate8Enum (drop 8 4 6)) (gate8Complement b) (gate8Complement a) = _
  rw [gate8_drop6]
  exact gate8_dualDrop6_table a b

end HiddenCircuits.Small
