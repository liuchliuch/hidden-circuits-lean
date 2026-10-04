import HiddenCircuits.FilterTheorem
import HiddenCircuits.Small.Mix

namespace HiddenCircuits
open Small

def codeIndex : Fin 2 → Fin 6 := ![1,3]
def oneBitCode (b : Fin 2) : State 4 2 := states2 (codeIndex b)

/-- Actual projected one-bit action, extracted at the two raw code states. -/
def oneBitEncoded (w : List (Letter 4)) : Matrix (Fin 2) (Fin 2) ℚ :=
  (localFilter 2 * wordMatrix 2 w * localFilter 2).submatrix oneBitCode oneBitCode

 theorem oneBitEncoded_compressed (w : List (Letter 4)) :
    oneBitEncoded w =
      (Theta2 * compress enum2 (wordMatrix 2 w) * Theta2).submatrix codeIndex codeIndex := by
  have h : compress enum2 (localFilter 2 * wordMatrix 2 w * localFilter 2) =
      Theta2 * compress enum2 (wordMatrix 2 w) * Theta2 := by
    simp only [compress_mul, localFilter2]
  exact congrArg (fun M => M.submatrix codeIndex codeIndex) h

 theorem oneBit_R : oneBitEncoded [⟨.R,0⟩] = !![1,0;1,0] := by
  rw [oneBitEncoded_compressed, compress_word]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Letter.matrix, rise2_0]
  decide +kernel

 theorem oneBit_E : oneBitEncoded [⟨.E,0⟩] = !![1,1;0,0] := by
  rw [oneBitEncoded_compressed, compress_word]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Letter.matrix, dualDrop2_0]
  decide +kernel

 theorem oneBit_Q : oneBitEncoded [⟨.B,1⟩] = !![2,0;0,1] := by
  rw [oneBitEncoded_compressed, compress_word]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Letter.matrix, dualRise2_1]
  decide +kernel

 theorem oneBit_A : oneBitEncoded [⟨.D,2⟩] = !![-1,0;0,1/2] := by
  rw [oneBitEncoded_compressed, compress_word]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Letter.matrix, drop2_2]
  decide +kernel

 theorem filterT_compressed : compress enum2 (wordMatrix 2 filterT) = Suffix2_10 := by
  rw [compress_word]
  simp only [filterT, filterZ, filterJ, List.map_append, List.map_cons, List.map_nil,
    Letter.matrix, rise2_1, drop2_2, rise2_2, dualRise2_1, rise2_0, dualDrop2_2]
  exact suffix2_10

 theorem oneBit_T : oneBitEncoded filterT = !![0,8;8,0] := by
  rw [oneBitEncoded_compressed, filterT_compressed]
  decide +kernel

 def mixingWord : List (Letter 4) :=
  [⟨.D,1⟩,⟨.B,1⟩,⟨.B,0⟩,⟨.B,1⟩,⟨.R,1⟩,⟨.R,2⟩]

 theorem mixingWord_compressed : compress enum2 (wordMatrix 2 mixingWord) = MixSuffix0 := by
  rw [compress_word]
  simp only [mixingWord, List.map_cons, List.map_nil, Letter.matrix,
    drop2_1, dualRise2_1, dualRise2_0, rise2_1, rise2_2]
  exact mixSuffix0

 theorem oneBit_mix : oneBitEncoded mixingWord = !![-2,4;4,8] := by
  rw [oneBitEncoded_compressed, mixingWord_compressed]
  decide +kernel

/-- The three separately projected operations give exactly the paper's normalized Hadamard. -/
theorem oneBit_H : oneBitEncoded [⟨.D,2⟩] * oneBitEncoded mixingWord *
    oneBitEncoded [⟨.D,2⟩] = (-2 : ℚ) • !![1,1;1,-1] := by
  rw [oneBit_A, oneBit_mix]
  decide +kernel

end HiddenCircuits
