import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCellParts

/-! The outer interpolation weight, with no graph-probe interpolation stage. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.WordRatio
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph RatioCell
set_option maxHeartbeats 800000

def ratio (d : ℕ) (t : Fin (d+1)) (answer : ℕ) : ℤ×ℤ :=
  ((answer:ℤ)*interpolationNegativeNumerator d t,interpolationDenominator d t)
noncomputable def constants : OracleBlock 52 := seq (prepend 11 (signedBits 1))
  (seq (prepend 12 (signedBits 1)) (seq (prepend 13 (signedBits 1)) (prepend 14 (signedBits 1))))
noncomputable def program : OracleBlock 52 := seq left (seq constants (seq copyAnswer combine))
noncomputable def time (d answer B : ℕ) : ℕ := GridWeightsRuntime.pairTime.eval d+
  5*(signedBits (answer:ℤ)).length+RatioCombine.time.eval B+42

lemma constants_executes (g : BitString→ℕ) (t k s l p h : ℕ) (answer dt nt : BitString) :
    constants.Executes g (state t k s l p h answer [] [] (fields dt nt [] [] [] [] []))
      (state t k s l p h answer [] [] (fields dt nt (signedBits 1) (signedBits 1) (signedBits 1) (signedBits 1) [])) 34 := by
  let s0:=state t k s l p h answer [] [] (fields dt nt [] [] [] [] [])
  let s1:=state t k s l p h answer [] [] (fields dt nt (signedBits 1) [] [] [] [])
  let s2:=state t k s l p h answer [] [] (fields dt nt (signedBits 1) (signedBits 1) [] [] [])
  let s3:=state t k s l p h answer [] [] (fields dt nt (signedBits 1) (signedBits 1) (signedBits 1) [] [])
  let s4:=state t k s l p h answer [] [] (fields dt nt (signedBits 1) (signedBits 1) (signedBits 1) (signedBits 1) [])
  have h1:(prepend (11:Fin 53) (signedBits 1)).Executes g s0 s1 7 := by
    convert prepend_executes g (11:Fin 53) (signedBits 1) s0 using 1
    funext i;fin_cases i <;> rfl
  have h2:(prepend (12:Fin 53) (signedBits 1)).Executes g s1 s2 7 := by
    convert prepend_executes g (12:Fin 53) (signedBits 1) s1 using 1
    funext i;fin_cases i <;> rfl
  have h3:(prepend (13:Fin 53) (signedBits 1)).Executes g s2 s3 7 := by
    convert prepend_executes g (13:Fin 53) (signedBits 1) s2 using 1
    funext i;fin_cases i <;> rfl
  have h4:(prepend (14:Fin 53) (signedBits 1)).Executes g s3 s4 7 := by
    convert prepend_executes g (14:Fin 53) (signedBits 1) s3 using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4))

lemma program_executes (g : BitString→ℕ) (d : ℕ) (t : Fin (d+1)) (s l p h answer B : ℕ)
    (hB : RegisterMachine.Bounded B (RatioCombine.registers 1 (answer:ℤ)
      (interpolationNegativeNumerator d t) 1 (interpolationDenominator d t) 1 1)) :
    ∃c,program.Executes g (state t.val (d-t.val) s l p h (signedBits (answer:ℤ)) [] [] (fields [] [] [] [] [] [] []))
      (state t.val (d-t.val) s l p h (signedBits (answer:ℤ))
        (signedBits (ratio d t answer).1) (signedBits (ratio d t answer).2) (fields [] [] [] [] [] [] [])) c ∧ c≤time d answer B := by
  obtain ⟨a,ha,hab⟩:=left_executes g d t s l p h (signedBits (answer:ℤ))
  have hb:=constants_executes g t.val (d-t.val) s l p h (signedBits (answer:ℤ))
    (signedBits (interpolationDenominator d t)) (signedBits (interpolationNegativeNumerator d t))
  have hc:=copyAnswer_executes g t.val (d-t.val) s l p h (signedBits (answer:ℤ))
    (signedBits (interpolationDenominator d t)) (signedBits (interpolationNegativeNumerator d t))
    (signedBits 1) (signedBits 1) (signedBits 1) (signedBits 1)
  obtain ⟨b,hd,hdb⟩:=combine_executes g t.val (d-t.val) s l p h (answer:ℤ)
    (interpolationNegativeNumerator d t) 1 (interpolationDenominator d t) 1 1 1 B hB
  simp only [one_mul,mul_one] at hd
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  unfold time
  omega
end HiddenCircuits.GraphReduction.Runtime.PairEval.WordRatio
