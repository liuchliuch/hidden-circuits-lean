import HiddenCircuits.Small.Gate8Suffix17
import HiddenCircuits.Small.Gate8R0

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8Suffix16Rows : Fin 70 → List (Fin 70 × ℚ) := ![[(12,-2560), (40,-1024), (42,512), (51,-10240), (61,4608)],
  [(12,-1792), (40,-1024), (42,512), (51,-4096), (61,4608)],
  [(10,256), (12,-512), (40,-512), (61,3072)],
  [(10,256), (12,512), (40,-512), (51,4096), (61,3072)],
  [(10,-256), (12,768), (40,512), (51,4096), (61,1536)],
  [(40,-512), (42,256), (51,-2048), (61,3072)],
  [(40,-256), (61,2048)],
  [(40,-256), (51,2048), (61,2048)],
  [(40,256), (51,2048), (61,1024)],
  [(40,-256), (61,2048)],
  [(40,-256), (61,2048)],
  [(40,256), (61,1024)],
  [(42,-256), (51,-1024), (61,1024)],
  [(42,-128), (51,-512), (61,512)],
  [(42,-128), (51,-512), (61,512)],
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
def Gate8Suffix16 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8Suffix16Rows
theorem gate8_suffix_step16 : (fun a => sparseMultiplyRow (Gate8R0Rows a) Gate8Suffix17Rows) = Gate8Suffix16Rows := by
  decide +kernel
theorem gate8_suffix16 : ([Gate8R0, Gate8E2, Gate8D2, Gate8R2, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6, Gate8R5, Gate8D6, Gate8R6, Gate8B5, Gate8R6, Gate8R5, Gate8R4, Gate8E6, Gate8D6, Gate8R6]).prod = Gate8Suffix16 := by
  rw [List.prod_cons, gate8_suffix17]
  exact (sparseMatrix_mul_sparseMatrix Gate8R0Rows Gate8Suffix17Rows).trans
    (congrArg sparseMatrix gate8_suffix_step16)

end HiddenCircuits.Small
