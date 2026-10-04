import HiddenCircuits.Small.Gate8States
import HiddenCircuits.LocalFilter

namespace HiddenCircuits
open Small
open scoped BigOperators

/-- Shift the original twenty-letter four-track filter to either block of eight tracks. -/
def twoBitFilterLetter (b : Fin 2) (l : Letter 4) : Letter 8 :=
  ⟨l.kind, ⟨4 * b.val + l.index.val, by have hb := b.isLt; have hi := l.index.isLt; omega⟩⟩

def twoBitFilterWord (b : Fin 2) : List (Letter 8) := filterWord.map (twoBitFilterLetter b)

def twoBitFilter (b : Fin 2) : Matrix (State 8 4) (State 8 4) ℚ :=
  (1 / 64 : ℚ) • wordMatrix 4 (twoBitFilterWord b)

/-- The actual stabilized eight-track projection from Lemma 6.1. -/
def twoBitProjection : Matrix (State 8 4) (State 8 4) ℚ :=
  (twoBitFilter 0 * twoBitFilter 1) ^ 6

def twoBitCodeIndex : Fin 4 → Fin 70 := ![20,22,40,42]
def twoBitCode (b : Fin 4) : State 8 4 := gate8States (twoBitCodeIndex b)

/-- Raw code states 10101010,10100110,01101010,01100110, in this order. -/
theorem twoBitCode_states : twoBitCode =
    ![⟨{0,2,4,6}, by decide⟩, ⟨{0,2,5,6}, by decide⟩,
      ⟨{1,2,4,6}, by decide⟩, ⟨{1,2,5,6}, by decide⟩] := by
  decide +kernel

def twoBitEncoded (w : List (Letter 8)) : Matrix (Fin 4) (Fin 4) ℚ :=
  (twoBitProjection * wordMatrix 4 w * twoBitProjection).submatrix twoBitCode twoBitCode

theorem twoBitFilter_sweep : twoBitFilter 0 * twoBitFilter 1 =
    (1/4096 : ℚ) • wordMatrix 4 (twoBitFilterWord 0 ++ twoBitFilterWord 1) := by
  rw [wordMatrix_append]
  simp only [twoBitFilter, smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num

end HiddenCircuits
