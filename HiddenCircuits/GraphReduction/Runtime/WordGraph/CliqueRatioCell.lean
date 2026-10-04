import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRatioParts
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRecoveryAlgebra

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRatioCell
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 500000
noncomputable def program (mode : Bool) : OracleBlock 52 := seq left (seq right (seq (norm mode)
  (seq copyAnswer combine)))

def componentBound (mode : Bool) (w : WordInstance) (q : Recovery.Index w) (answer : ℕ) (B : ℕ) : Prop :=
  RegisterMachine.Bounded B (RatioCombine.registers
    ((-1:ℤ)^(CliqueRecovery.signExponent mode w.particles (Recovery.height w q.1))) (answer:ℤ)
    (interpolationNegativeNumerator (Recovery.degree w) q.1) (EvenWeights.numerator (Recovery.innerDegree w q.1) q.2)
    (interpolationDenominator (Recovery.degree w) q.1) (EvenWeights.denominator (Recovery.innerDegree w q.1) q.2)
    ((oddFactorial q.2.val:ℤ)^(CliqueRecovery.normalizationExponent mode (Recovery.height w q.1))))

noncomputable def costBound (w : WordInstance) (q : Recovery.Index w) (answer B : ℕ) : ℕ :=
  GridWeightsRuntime.pairTime.eval (Recovery.degree w)+EvenWeightsRuntime.time.eval (Recovery.innerDegree w q.1)+
  OddFactorialNormalization.time.eval (q.2.val+Recovery.height w q.1+w.particles)+
  5*(signedBits (answer:ℤ)).length+RatioCombine.time.eval B+10

lemma exponent_eq (mode : Bool) (h : ℕ) : OddFactorialNormalization.exponent mode h=CliqueRecovery.normalizationExponent mode h := by
  cases mode <;> simp [OddFactorialNormalization.exponent,CliqueRecovery.normalizationExponent]
lemma sign_eq (mode : Bool) (h p : ℕ) : OddFactorialNormalization.signValue mode h p=(-1:ℤ)^(CliqueRecovery.signExponent mode p h) := by
  cases mode <;> simp [OddFactorialNormalization.signValue,CliqueRecovery.signExponent]

theorem program_executes (g : BitString → ℕ) (mode : Bool) (w : WordInstance) (q : Recovery.Index w) (answer B : ℕ)
    (hB : componentBound mode w q answer B) :
    ∃c, (program mode).Executes g
      (state q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
        w.particles (Recovery.height w q.1) (signedBits (answer:ℤ)) [] [] (fields [] [] [] [] [] [] []))
      (state q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
        w.particles (Recovery.height w q.1) (signedBits (answer:ℤ))
        (signedBits (CliqueRecovery.ratio mode w q answer).1) (signedBits (CliqueRecovery.ratio mode w q answer).2)
        (fields [] [] [] [] [] [] [])) c ∧ c≤costBound w q answer B := by
  let nt := signedBits (interpolationNegativeNumerator (Recovery.degree w) q.1)
  let dt := signedBits (interpolationDenominator (Recovery.degree w) q.1)
  let ns := signedBits (EvenWeights.numerator (Recovery.innerDegree w q.1) q.2)
  let ds := signedBits (EvenWeights.denominator (Recovery.innerDegree w q.1) q.2)
  obtain ⟨a,ha,hab⟩ := left_executes g (Recovery.degree w) q.1 q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) (signedBits (answer:ℤ))
  obtain ⟨b,hb,hbb⟩ := right_executes g (Recovery.innerDegree w q.1) q.2 q.1.val (Recovery.degree w-q.1.val)
    w.particles (Recovery.height w q.1) (signedBits (answer:ℤ)) dt nt
  obtain ⟨c,hc,hcb⟩ := norm_executes g mode q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) (signedBits (answer:ℤ)) dt nt ds ns
  rw [exponent_eq,sign_eq] at hc
  have hd := copyAnswer_executes g q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) (signedBits (answer:ℤ)) dt nt ds ns
    (signedBits ((oddFactorial q.2.val:ℤ)^(CliqueRecovery.normalizationExponent mode (Recovery.height w q.1))))
    (signedBits ((-1:ℤ)^(CliqueRecovery.signExponent mode w.particles (Recovery.height w q.1))))
  obtain ⟨e,he,heb⟩ := combine_executes g q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) (answer:ℤ)
    (interpolationNegativeNumerator (Recovery.degree w) q.1) (EvenWeights.numerator (Recovery.innerDegree w q.1) q.2)
    (interpolationDenominator (Recovery.degree w) q.1) (EvenWeights.denominator (Recovery.innerDegree w q.1) q.2)
    ((oddFactorial q.2.val:ℤ)^(CliqueRecovery.normalizationExponent mode (Recovery.height w q.1)))
    ((-1:ℤ)^(CliqueRecovery.signExponent mode w.particles (Recovery.height w q.1))) B hB
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc (seq_executes _ _ g hd he))),by unfold costBound;omega⟩

lemma program_queryFree (mode : Bool) : (program mode).QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ GridWeightsRuntime.pairProgram_queryFree)
  (seq_queryFree _ _ (rename_queryFree _ _ EvenWeightsRuntime.program_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ (OddFactorialNormalization.program_queryFree mode))
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ RatioCombine.program_queryFree))))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRatioCell
