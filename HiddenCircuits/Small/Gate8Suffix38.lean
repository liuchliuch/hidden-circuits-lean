import HiddenCircuits.Small.Gate8Suffix39
import HiddenCircuits.Small.Gate8D6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix38Rows : Fin 70 → List (Fin 70 × ℚ) := ![[(0,1)],
  [(1,1)],
  [(2,1)],
  [(3,1)],
  [(3,1)],
  [(5,1)],
  [(6,1)],
  [(7,1)],
  [(7,1)],
  [(9,1)],
  [(10,1)],
  [(10,1)],
  [(12,1)],
  [(12,1)],
  [],
  [(15,1)],
  [(16,1)],
  [(17,1)],
  [(17,1)],
  [(19,1)],
  [(20,1)],
  [(20,1)],
  [(22,1)],
  [(22,1)],
  [],
  [(25,1)],
  [(26,1)],
  [(26,1)],
  [(28,1)],
  [(28,1)],
  [],
  [(31,1)],
  [(31,1)],
  [],
  [],
  [(35,1)],
  [(36,1)],
  [(37,1)],
  [(37,1)],
  [(39,1)],
  [(40,1)],
  [(40,1)],
  [(42,1)],
  [(42,1)],
  [],
  [(45,1)],
  [(46,1)],
  [(46,1)],
  [(48,1)],
  [(48,1)],
  [],
  [(51,1)],
  [(51,1)],
  [],
  [],
  [(55,1)],
  [(56,1)],
  [(56,1)],
  [(58,1)],
  [(58,1)],
  [],
  [(61,1)],
  [(61,1)],
  [],
  [],
  [(65,1)],
  [(65,1)],
  [],
  [],
  []]
def Gate8Suffix38 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix38Rows
theorem gate8_suffix_step38 : (fun a => sparseMultiplyRow (Gate8D6Rows a) Gate8Suffix39Rows) = Gate8Suffix38Rows := by
  decide +kernel
theorem gate8_suffix38 : ([Gate8D6, Gate8R6]).prod = Gate8Suffix38 := by
  rw [List.prod_cons, gate8_suffix39]
  exact (sparseMatrix_mul_sparseMatrix Gate8D6Rows Gate8Suffix39Rows).trans
    (congrArg sparseMatrix gate8_suffix_step38)

end HiddenCircuits.Small
