import HiddenCircuits.Small.Gate8Suffix27
import HiddenCircuits.Small.Gate8R4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix26Rows : Fin 70 → List (Fin 70 × ℚ) := ![[],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(10,-32)],
  [(12,16)],
  [],
  [(12,16)],
  [],
  [],
  [],
  [],
  [],
  [],
  [(20,-32)],
  [(22,16)],
  [],
  [(22,16)],
  [],
  [],
  [(26,-32)],
  [(28,16)],
  [],
  [(28,16)],
  [],
  [],
  [(31,64)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(40,-32)],
  [(42,16)],
  [],
  [(42,16)],
  [],
  [],
  [(46,-32)],
  [(48,16)],
  [],
  [(48,16)],
  [],
  [],
  [(51,64)],
  [],
  [],
  [],
  [(56,-32)],
  [(58,16)],
  [],
  [(58,16)],
  [],
  [],
  [(61,64)],
  [],
  [],
  [],
  [(65,64)],
  [],
  [],
  [],
  []]
def Gate8Suffix26 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix26Rows
theorem gate8_suffix_step26 : (fun a => sparseMultiplyRow (Gate8R4Rows a) Gate8Suffix27Rows) = Gate8Suffix26Rows := by
  decide +kernel
theorem gate8_suffix26 : ([Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix26 := by
  rw [List.prod_cons, gate8_suffix27]
  exact (sparseMatrix_mul_sparseMatrix Gate8R4Rows Gate8Suffix27Rows).trans
    (congrArg sparseMatrix gate8_suffix_step26)

end HiddenCircuits.Small
