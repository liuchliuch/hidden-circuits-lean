import HiddenCircuits.Circuit.PhysicalLift
import HiddenCircuits.Circuit.SharedDiagonal
import HiddenCircuits.GlobalOneBit

namespace HiddenCircuits.Circuit

def ScaledWord.rescale {k : ℕ} (w : ScaledWord k) (c : ℚ) : ScaledWord k :=
  ⟨c*w.scalar,w.word⟩

 theorem ScaledWord.rescale_matrix {k : ℕ} (w : ScaledWord k) (c : ℚ) :
    (w.rescale c).matrix=c • w.matrix := by
  simp only [ScaledWord.rescale,ScaledWord.matrix,smul_smul]

/-- Literal one-block implementation of every primitive one-bit gate. -/
def oneGateWord : OneGate → ScaledWord 1
  | .reset => ⟨1,[⟨.R,(0:Fin 3)⟩]⟩
  | .copy => ⟨1,[⟨.E,(0:Fin 3)⟩]⟩
  | .scale => ⟨1,[⟨.B,(1:Fin 3)⟩]⟩
  | .signScale => ⟨1,[⟨.D,(2:Fin 3)⟩]⟩
  | .swap => ⟨1/8,filterT⟩
  | .mix => ⟨1,mixingWord⟩
  | .encodedSwap => ⟨1,filterT⟩
  | .hadamard =>
      let u : ScaledWord 1 := ⟨1,[⟨.D,(2:Fin 3)⟩]⟩
      let v : ScaledWord 1 := ⟨1,mixingWord⟩
      let w := (u.compose v).compose u
      w.rescale (-1/2)

 theorem encoded_oneBit_entry (w : List (Letter 4)) (x y : Fin 2) :
    encoded (k:=1) (wordMatrix 2 w) (oneBitEquiv x) (oneBitEquiv y) = oneBitEncoded w x y := by
  rw [encoded_entry]
  exact global_oneBit_encoded w x y

 theorem oneGateWord_matrix (g : OneGate) : (oneGateWord g).matrix=g.logical := by
  have basic (w : List (Letter 4)) (c : ℚ) :
      (ScaledWord.matrix (k:=1) ⟨c,w⟩).submatrix oneBitEquiv oneBitEquiv = c • oneBitEncoded w := by
    ext x y
    simp only [ScaledWord.matrix,Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul]
    exact congrArg (fun z : ℚ => c*z) (encoded_oneBit_entry w x y)
  have smulSub (c : ℚ) (A : Matrix (CodeBits 1) (CodeBits 1) ℚ) :
      (c • A).submatrix oneBitEquiv oneBitEquiv=c • A.submatrix oneBitEquiv oneBitEquiv := rfl
  have mulSub (A B : Matrix (CodeBits 1) (CodeBits 1) ℚ) :
      (A*B).submatrix oneBitEquiv oneBitEquiv=
        A.submatrix oneBitEquiv oneBitEquiv * B.submatrix oneBitEquiv oneBitEquiv :=
    Matrix.submatrix_mul _ _ _ _ _ oneBitEquiv.bijective
  have injective (A B : Matrix (CodeBits 1) (CodeBits 1) ℚ)
      (h : A.submatrix oneBitEquiv oneBitEquiv=B.submatrix oneBitEquiv oneBitEquiv) : A=B := by
    ext x y
    obtain ⟨a,rfl⟩ := oneBitEquiv.surjective x
    obtain ⟨b,rfl⟩ := oneBitEquiv.surjective y
    exact congrFun (congrFun h a) b
  apply injective
  have hr : (g.logical).submatrix oneBitEquiv oneBitEquiv=g.matrix := by
    ext x y
    simp [OneGate.logical]
  rw [hr]
  cases g with
  | reset => rw [oneGateWord,basic,oneBit_R,one_smul]; rfl
  | copy => rw [oneGateWord,basic,oneBit_E,one_smul]; rfl
  | scale => rw [oneGateWord,basic,oneBit_Q,one_smul]; rfl
  | signScale => rw [oneGateWord,basic,oneBit_A,one_smul]; rfl
  | swap =>
    rw [oneGateWord,basic,oneBit_T]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [OneGate.matrix]
  | mix => rw [oneGateWord,basic,oneBit_mix,one_smul]; rfl
  | encodedSwap => rw [oneGateWord,basic,oneBit_T,one_smul]; rfl
  | hadamard =>
    rw [oneGateWord,ScaledWord.rescale_matrix,ScaledWord.compose_matrix,ScaledWord.compose_matrix]
    simp only [smulSub,mulSub,basic,one_smul]
    change (-1/2:ℚ) • (oneBitEncoded [⟨.D,2⟩] * oneBitEncoded mixingWord *
      oneBitEncoded [⟨.D,2⟩]) = OneGate.hadamard.matrix
    rw [oneBit_H]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [OneGate.matrix]

/-- All one-bit operations at arbitrary places are implemented by explicit elementary words. -/
def placedOneGateWord {n : ℕ} (p : Placement n 1) (g : OneGate) : ScaledWord n :=
  (oneGateWord g).lift p

 theorem placedOneGateWord_matrix {n : ℕ} (p : Placement n 1) (g : OneGate) :
    (placedOneGateWord p g).matrix=p.lift g.logical := by
  rw [placedOneGateWord,ScaledWord.lift_matrix,oneGateWord_matrix]

end HiddenCircuits.Circuit
