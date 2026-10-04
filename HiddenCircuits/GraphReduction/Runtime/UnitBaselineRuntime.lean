import HiddenCircuits.GraphReduction.Runtime.UnitBaselineChoice

/-! Adaptation: classifier selection is performed by the literal branch
tree in UnitBaselineChoice; its separate identity prefix costs one instruction. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitBaseline
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

lemma signedBits_length_le_abs (z : ℤ) : (signedBits z).length≤z.natAbs+1 := by
  have h : Nat.size z.natAbs≤z.natAbs := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [signedBits,List.length_cons,encodeNat_length]
  omega

def inputBound (width height : ℕ) (x : VertexRecord) : ℕ := width+height+x.layer+x.track+1002
lemma init_bounded (width height : ℕ) (x : VertexRecord) :
    Bounded (inputBound width height x) (init width height x.layer x.track) := by
  intro i
  have h := signedBits_length_le_abs (init width height x.layer x.track i)
  fin_cases i <;> simp [init,inputBound] at h ⊢ <;> omega

noncomputable def timePolynomial : Polynomial ℕ :=
  straightTime (code .probe)+straightTime (code .even)+straightTime (code .ordinary)+
  straightTime (code .risePlus)+straightTime (code .riseMinus)+straightTime (code .dropPlus)+
  straightTime (code .dropMinus)+300
lemma choiceTime_bound (m : Mode) (B : ℕ) : (straightTime (code m)).eval B+288≤timePolynomial.eval B := by
  cases m <;> simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_ofNat] <;> omega

 theorem program_executes (width height : ℕ) (x : VertexRecord) (g : BitString → ℕ) :
    ∃ t, program.Executes g (store (init width height x.layer x.track) x 0)
      (store (evaluate (code (mode x)) (init width height x.layer x.track)) x 0) t ∧
      t≤timePolynomial.eval (inputBound width height x) := by
  have hc := classify_executes g (init width height x.layer x.track) x
  obtain ⟨t,ht,hb⟩ := choose_executes g (init width height x.layer x.track) x (inputBound width height x)
    (init_bounded width height x) (code_valid (mode x) width height x.layer x.track)
  refine ⟨1+t+2,seq_executes _ _ g hc ht,?_⟩
  have h := choiceTime_bound (mode x) (inputBound width height x)
  omega

 theorem result_value (width height : ℕ) (x : VertexRecord) :
    evaluate (code (mode x)) (init width height x.layer x.track) 2=
      if x.probe then (2*(x.layer:ℤ)+1)*UnitInterval.commonLength width height else
        (2*(x.layer:ℤ)+(if x.side then 1 else 0))*UnitInterval.commonLength width height+offsetBase (UnitInterval.scale height) x := by
  rw [code_value,mode_value]

 theorem result_bounded (width height : ℕ) (x : VertexRecord) :
    Bounded (2^16*(inputBound width height x+3))
      (evaluate (code (mode x)) (init width height x.layer x.track)) := by
  have h := (safe_of_bounded (code (mode x)) (init width height x.layer x.track) (inputBound width height x)
    (init_bounded width height x) (code_valid (mode x) width height x.layer x.track)).final
  apply h.mono
  have hp : (2:ℕ)^(code (mode x)).length≤2^16 := by cases mode x <;> decide +kernel
  exact Nat.mul_le_mul_right _ hp

end HiddenCircuits.GraphReduction.Runtime.UnitBaseline
