import HiddenCircuits.Small.Gate8Suffix19
import HiddenCircuits.Small.Gate8D2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix18Rows : Fin 70 → List (Fin 70 × ℚ) := ![[(10,-128), (12,64)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(10,64)],
  [(10,64)],
  [(10,-64)],
  [(12,64)],
  [(12,32)],
  [(12,32)],
  [(20,256), (22,-128), (31,-768)],
  [(20,128), (31,-512)],
  [(20,128), (31,-512)],
  [(20,-128), (31,-256)],
  [(20,64)],
  [(20,64)],
  [(20,-64)],
  [(22,64)],
  [(22,32)],
  [(22,32)],
  [(20,64)],
  [(20,64)],
  [(20,-64)],
  [(22,64)],
  [(22,32)],
  [(22,32)],
  [(31,256)],
  [(31,128)],
  [(31,128)],
  [],
  [(40,256), (42,-128), (51,-768)],
  [(40,128), (51,-512)],
  [(40,128), (51,-512)],
  [(40,-128), (51,-256)],
  [(40,64)],
  [(40,64)],
  [(40,-64)],
  [(42,64)],
  [(42,32)],
  [(42,32)],
  [(40,64)],
  [(40,64)],
  [(40,-64)],
  [(42,64)],
  [(42,32)],
  [(42,32)],
  [(51,256)],
  [(51,128)],
  [(51,128)],
  [],
  [(61,1024)],
  [(61,1024)],
  [(61,512)],
  [(61,512)],
  [(61,256)],
  [(61,256)],
  [(61,256)],
  [(61,128)],
  [(61,128)],
  [],
  [(61,256)],
  [(61,128)],
  [(61,128)],
  [],
  []]
def Gate8Suffix18 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix18Rows
theorem gate8_suffix_step18 : (fun a => sparseMultiplyRow (Gate8D2Rows a) Gate8Suffix19Rows) = Gate8Suffix18Rows := by
  decide +kernel
theorem gate8_suffix18 : ([Gate8D2, Gate8R2, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix18 := by
  rw [List.prod_cons, gate8_suffix19]
  exact (sparseMatrix_mul_sparseMatrix Gate8D2Rows Gate8Suffix19Rows).trans
    (congrArg sparseMatrix gate8_suffix_step18)

end HiddenCircuits.Small
