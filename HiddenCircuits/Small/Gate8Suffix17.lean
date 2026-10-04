import HiddenCircuits.Small.Gate8Suffix18
import HiddenCircuits.Small.Gate8E2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix17Rows : Fin 70 → List (Fin 70 × ℚ) := ![[(12,-1280)],
  [(12,-896)],
  [(10,128), (12,-256)],
  [(10,128), (12,256)],
  [(10,-128), (12,384)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(20,256), (22,-128), (31,1024)],
  [(20,128)],
  [(20,128), (31,-1024)],
  [(20,-128), (31,-1024)],
  [(20,128)],
  [(20,128)],
  [(20,-128)],
  [(22,128), (31,512)],
  [(22,64), (31,256)],
  [(22,64), (31,256)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(40,256), (42,-128), (51,1024)],
  [(40,128)],
  [(40,128), (51,-1024)],
  [(40,-128), (51,-1024)],
  [(40,128)],
  [(40,128)],
  [(40,-128)],
  [(42,128), (51,512)],
  [(42,64), (51,256)],
  [(42,64), (51,256)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(61,1024)],
  [(61,1024)],
  [(61,512)],
  [(61,512)],
  [(61,256)],
  [(61,256)],
  [(61,512)],
  [(61,256)],
  [(61,256)],
  [],
  [],
  [],
  [],
  [],
  []]
def Gate8Suffix17 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix17Rows
theorem gate8_suffix_step17 : (fun a => sparseMultiplyRow (Gate8E2Rows a) Gate8Suffix18Rows) = Gate8Suffix17Rows := by
  decide +kernel
theorem gate8_suffix17 : ([Gate8E2, Gate8D2, Gate8R2, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix17 := by
  rw [List.prod_cons, gate8_suffix18]
  exact (sparseMatrix_mul_sparseMatrix Gate8E2Rows Gate8Suffix18Rows).trans
    (congrArg sparseMatrix gate8_suffix_step17)

end HiddenCircuits.Small
