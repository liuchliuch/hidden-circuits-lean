import HiddenCircuits.Circuit.OneGateWords
import HiddenCircuits.Circuit.WordCompilation
import HiddenCircuits.TwoBitGlobal

namespace HiddenCircuits.Circuit

/-- The same lexicographic00,01,10,11 identification used in the checked gate certificate. -/
theorem twoBitEquiv_eq_lex : twoBitEquiv=twoBitLexEquiv := by
  ext i
  fin_cases i <;> rfl

def logicalG : Matrix (CodeBits 2) (CodeBits 2) ℚ :=
  G.submatrix twoBitEquiv.symm twoBitEquiv.symm

/-- The physical boundary letter R₃ implements the actual local G through both projections. -/
def twoGateWord : ScaledWord 2 := ⟨1,[⟨.R,(3:Fin 7)⟩]⟩

 theorem twoGateWord_matrix : twoGateWord.matrix=logicalG := by
  have h : twoGateWord.matrix.submatrix twoBitEquiv twoBitEquiv=G := by
    ext a b
    change (1:ℚ) * encoded (wordMatrix (2*2) [⟨.R,(3:Fin 7)⟩])
      (twoBitEquiv a) (twoBitEquiv b) = G a b
    rw [one_mul,wordMatrix_cons,wordMatrix_nil,mul_one,encoded_entry,twoBitEquiv_eq_lex]
    exact congrFun (congrFun global_twoBit_G a) b
  ext x y
  obtain ⟨a,rfl⟩ := twoBitEquiv.surjective x
  obtain ⟨b,rfl⟩ := twoBitEquiv.surjective y
  simpa [logicalG] using congrFun (congrFun h a) b

/-- An explicit adjacent-wire circuit over the fixed available gate set. -/
inductive AvailableGate (n : ℕ) where
  | one (p : Placement n 1) (g : OneGate)
  | interaction (p : Placement n 2)

def AvailableGate.matrix {n : ℕ} : AvailableGate n → Matrix (CodeBits n) (CodeBits n) ℚ
  | .one p g => p.lift g.logical
  | .interaction p => p.lift logicalG

def AvailableGate.compile {n : ℕ} : AvailableGate n → ScaledWord n
  | .one p g => placedOneGateWord p g
  | .interaction p => twoGateWord.lift p

 theorem AvailableGate.compile_matrix {n : ℕ} (g : AvailableGate n) : g.compile.matrix=g.matrix := by
  cases g with
  | one p g => exact placedOneGateWord_matrix p g
  | interaction p => rw [compile,ScaledWord.lift_matrix,twoGateWord_matrix]; rfl

 def availableCircuitMatrix {n : ℕ} (w : List (AvailableGate n)) : Matrix (CodeBits n) (CodeBits n) ℚ :=
  (w.map AvailableGate.matrix).prod

/-- Every actual available-gate circuit gives one genuine WordEval query and an exact scalar. -/
theorem availableCircuit_to_word {n : ℕ} (hn : 0<n) (w : List (AvailableGate n)) (x y : CodeBits n) :
    availableCircuitMatrix w x y = closedScalar (w.map AvailableGate.compile) *
      (compileWordInstance hn (w.map AvailableGate.compile) x y).value := by
  have h := compileWordInstance_correct hn (w.map AvailableGate.compile) x y
  simpa only [List.map_map,Function.comp_def,AvailableGate.compile_matrix,availableCircuitMatrix] using h

/-- Fixed one-bit implementations, including the two intervening projection words in H. -/
theorem oneGateWord_length (g : OneGate) : (oneGateWord g).word.length≤88 := by
  cases g <;> decide +kernel

 theorem AvailableGate.compile_length {n : ℕ} (g : AvailableGate n) : g.compile.word.length≤88 := by
  cases g with
  | one p g => simpa only [compile,placedOneGateWord,ScaledWord.lift_length] using oneGateWord_length g
  | interaction p => simp [compile,ScaledWord.lift_length,twoGateWord]

/-- Explicit polynomial elementary-word size for every emitted oracle instance. -/
theorem availableCircuit_word_length_bound {n : ℕ} (hn : 0<n) (w : List (AvailableGate n))
    (x y : CodeBits n) :
    (compileWordInstance hn (w.map AvailableGate.compile) x y).word.length ≤
      88*w.length+(w.length+2)*(40*n^3+40*n) := by
  have hs : ((w.map AvailableGate.compile).map (fun u => u.word.length)).sum≤88*w.length := by
    induction w with
    | nil => simp
    | cons g w ih =>
      have hg := g.compile_length
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  change ((closedWord (w.map AvailableGate.compile)).map (Letter.castTracks _)).length≤_
  rw [List.length_map]
  exact (closedWord_length_bound _).trans (by simp only [List.length_map]; omega)

end HiddenCircuits.Circuit
