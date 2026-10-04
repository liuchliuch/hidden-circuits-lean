import HiddenCircuits.Small.Gate8Suffix30
import HiddenCircuits.Small.Gate8R6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix29Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(12,8)],
  [(12,8)],
  [(12,8)],
  [(10,8)],
  [(10,8)],
  [(10,8)],
  [],
  [],
  [],
  [],
  [(22,8)],
  [(22,8)],
  [(22,8)],
  [(20,8)],
  [(20,8)],
  [(20,8)],
  [(28,8)],
  [(28,8)],
  [(28,8)],
  [(26,8)],
  [(26,8)],
  [(26,8)],
  [(31,16)],
  [(31,16)],
  [(31,16)],
  [],
  [],
  [],
  [],
  [],
  [(42,8)],
  [(42,8)],
  [(42,8)],
  [(40,8)],
  [(40,8)],
  [(40,8)],
  [(48,8)],
  [(48,8)],
  [(48,8)],
  [(46,8)],
  [(46,8)],
  [(46,8)],
  [(51,16)],
  [(51,16)],
  [(51,16)],
  [],
  [(58,8)],
  [(58,8)],
  [(58,8)],
  [(56,8)],
  [(56,8)],
  [(56,8)],
  [(61,16)],
  [(61,16)],
  [(61,16)],
  [],
  [(65,16)],
  [(65,16)],
  [(65,16)],
  [],
  []]
def Gate8Suffix29 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix29Rows
theorem gate8_suffix_step29 : (fun a => sparseMultiplyRow (Gate8R6Rows a) Gate8Suffix30Rows) = Gate8Suffix29Rows := by
  decide +kernel
theorem gate8_suffix29 : ([Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix29 := by
  rw [List.prod_cons, gate8_suffix30]
  exact (sparseMatrix_mul_sparseMatrix Gate8R6Rows Gate8Suffix30Rows).trans
    (congrArg sparseMatrix gate8_suffix_step29)

end HiddenCircuits.Small
