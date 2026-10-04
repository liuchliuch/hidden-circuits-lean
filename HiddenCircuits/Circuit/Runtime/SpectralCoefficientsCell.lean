import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsNegation
import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! The coefficient update prev−a*c is a literal fixed signed-arithmetic program. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCoefficients
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic
open HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine

def registers (a prev c out : ℤ) : Fin 7 → ℤ := fun i =>
  if i.val=0 then -a else if i.val=1 then prev else if i.val=2 then c else if i.val=3 then out else 0

def cellCode : List Instruction := [⟨.multiply,3,0,2⟩,⟨.add,3,1,3⟩]
noncomputable def arithmeticCell : OracleBlock 15 := compile cellCode
noncomputable def arithmeticTime : Polynomial ℕ := straightTime cellCode

theorem cell_evaluate (a prev c out : ℤ) :
    evaluate cellCode (registers a prev c out)=registers a prev c (prev-a*c) := by
  funext i
  fin_cases i <;> simp [evaluate,cellCode,Instruction.eval,Operation.eval,registers] <;> ring

theorem cell_valid (a prev c out : ℤ) : Valid cellCode (registers a prev c out) := by
  simp [Valid,cellCode,Operation.Valid]

@[simp] theorem signedBits_neg_length (a : ℤ) : (signedBits (-a)).length=(signedBits a).length := by
  simp [signedBits]

theorem arithmetic_executes (g : BitString → ℕ) (a prev c : ℤ) (B : ℕ)
    (ha : (signedBits a).length≤B) (hp : (signedBits prev).length≤B) (hc : (signedBits c).length≤B) :
    ∃ t, arithmeticCell.Executes g (RegisterMachine.store [] [] (signedBits ∘ registers a prev c 0))
      (RegisterMachine.store [] [] (signedBits ∘ registers a prev c (prev-a*c))) t ∧ t≤arithmeticTime.eval B := by
  have hB : 1≤B := by simp only [signedBits,List.length_cons] at ha;omega
  have hb : Bounded B (registers a prev c 0) := by
    intro i
    fin_cases i <;> simp only [registers,ite_true,ite_false,signedBits_neg_length]
    all_goals first | exact ha | exact hp | exact hc | exact hB
  simpa only [cell_evaluate] using compile_polynomial cellCode g (registers a prev c 0) B hb (cell_valid _ _ _ _)

theorem cell_output_length (a prev c : ℤ) (B : ℕ)
    (ha : (signedBits a).length≤B) (hp : (signedBits prev).length≤B) (hc : (signedBits c).length≤B) :
    (signedBits (prev-a*c)).length≤4*B+9 := by
  have ha' : (signedBits (-a)).length≤B := by simpa using ha
  have hm := operation_bitLength .multiply (-a) c B ha' hc
  have hp' : (signedBits prev).length≤2*B+3 := by omega
  have ht := operation_bitLength .add prev ((-a)*c) (2*B+3) hp' hm
  simpa only [Operation.eval,neg_mul,sub_eq_add_neg,show 2*(2*B+3)+3=4*B+9 by ring] using ht
end HiddenCircuits.Circuit.Runtime.SpectralCoefficients
