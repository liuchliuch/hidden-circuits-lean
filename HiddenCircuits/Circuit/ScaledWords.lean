import HiddenCircuits.Encoding
import HiddenCircuits.GlobalProjectionWord

namespace HiddenCircuits.Circuit

/-- A literal globally normalized elementary word together with its exact rational scalar. -/
structure ScaledWord (k : ℕ) where
  scalar : ℚ
  word : List (Letter (blockWidth k))

def ScaledWord.matrix {k : ℕ} (w : ScaledWord k) : Matrix (CodeBits k) (CodeBits k) ℚ :=
  w.scalar • encoded (wordMatrix (2*k) w.word)

 theorem encoded_smul {k : ℕ} (c : ℚ)
    (M : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ) :
    encoded (c • M)=c • encoded M := by
  simp only [encoded,Matrix.mul_smul,Matrix.smul_mul]

@[simp] theorem encoded_one (k : ℕ) :
    encoded (1 : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ)=1 := by
  simp only [encoded,Matrix.mul_one,encodingEL]

/-- Explicit projected composition, not unjustified multiplication of the unprojected words. -/
def ScaledWord.compose {k : ℕ} (u v : ScaledWord k) : ScaledWord k :=
  ⟨u.scalar*v.scalar*((1/64:ℚ)^(k*globalProjectionExponent k)),
    u.word ++ globalProjectionWord k ++ v.word⟩

 theorem ScaledWord.compose_matrix {k : ℕ} (u v : ScaledWord k) :
    (u.compose v).matrix=u.matrix*v.matrix := by
  simp only [ScaledWord.compose,ScaledWord.matrix,wordMatrix_append]
  rw [smul_mul_assoc,mul_smul_comm,smul_smul,encoded_mul,globalProjection_eq_word,
    mul_smul_comm,smul_mul_assoc,encoded_smul,smul_smul]

 theorem ScaledWord.compose_length {k : ℕ} (u v : ScaledWord k) :
    (u.compose v).word.length=u.word.length+v.word.length+(globalProjectionWord k).length := by
  simp only [ScaledWord.compose,List.length_append]
  omega

/-- The empty logical circuit is represented without an oracle request. -/
def ScaledWord.identity (k : ℕ) : ScaledWord k := ⟨1,[]⟩

@[simp] theorem ScaledWord.identity_matrix (k : ℕ) : (ScaledWord.identity k).matrix=1 := by
  simp [ScaledWord.identity,ScaledWord.matrix]

/-- Concrete compiler for a finite list of individually implemented gates. -/
def compileProjected {k : ℕ} : List (ScaledWord k) → ScaledWord k
  | [] => .identity k
  | u::w => u.compose (compileProjected w)

/-- Every inserted projection is the actual polynomial-length word, so compiled products are exact. -/
theorem compileProjected_matrix {k : ℕ} (w : List (ScaledWord k)) :
    (compileProjected w).matrix=(w.map ScaledWord.matrix).prod := by
  induction w with
  | nil => simp [compileProjected]
  | cons u w ih => simp only [compileProjected,ScaledWord.compose_matrix,List.map_cons,List.prod_cons,ih]

/-- Exact compiler letter count; there is one explicit projection per listed gate. -/
theorem compileProjected_length {k : ℕ} (w : List (ScaledWord k)) :
    (compileProjected w).word.length=(w.map (fun u => u.word.length)).sum +
      w.length*(globalProjectionWord k).length := by
  induction w with
  | nil => simp [compileProjected,ScaledWord.identity]
  | cons u w ih =>
    rw [compileProjected,ScaledWord.compose_length,ih]
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- A logical entry of any implemented gate circuit is a scalar times one actual physical word entry. -/
theorem compileProjected_entry {k : ℕ} (w : List (ScaledWord k)) (x y : CodeBits k) :
    ((w.map ScaledWord.matrix).prod) x y = (compileProjected w).scalar *
      (globalProjection k * wordMatrix (2*k) (compileProjected w).word * globalProjection k)
        (rawCode k x) (rawCode k y) := by
  rw [← compileProjected_matrix]
  simp only [ScaledWord.matrix,Matrix.smul_apply,smul_eq_mul,encoded_entry]

end HiddenCircuits.Circuit
