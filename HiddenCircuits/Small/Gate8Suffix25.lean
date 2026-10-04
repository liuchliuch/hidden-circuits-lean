import HiddenCircuits.Small.Gate8Suffix26
import HiddenCircuits.Small.Gate8R5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix25Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(10,-32)],
  [(10,-32)],
  [],
  [(12,32)],
  [],
  [],
  [],
  [],
  [],
  [],
  [(20,-32)],
  [(20,-32)],
  [],
  [(22,32)],
  [],
  [],
  [(26,-32)],
  [(26,-32)],
  [],
  [(28,32)],
  [],
  [],
  [(31,128)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(40,-32)],
  [(40,-32)],
  [],
  [(42,32)],
  [],
  [],
  [(46,-32)],
  [(46,-32)],
  [],
  [(48,32)],
  [],
  [],
  [(51,128)],
  [],
  [],
  [],
  [(56,-32)],
  [(56,-32)],
  [],
  [(58,32)],
  [],
  [],
  [(61,128)],
  [],
  [],
  [],
  [(65,128)],
  [],
  [],
  [],
  []]
def Gate8Suffix25 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix25Rows
theorem gate8_suffix_step25 : (fun a => sparseMultiplyRow (Gate8R5Rows a) Gate8Suffix26Rows) = Gate8Suffix25Rows := by
  decide +kernel
theorem gate8_suffix25 : ([Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix25 := by
  rw [List.prod_cons, gate8_suffix26]
  exact (sparseMatrix_mul_sparseMatrix Gate8R5Rows Gate8Suffix26Rows).trans
    (congrArg sparseMatrix gate8_suffix_step25)

end HiddenCircuits.Small
