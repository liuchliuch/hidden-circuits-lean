import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCellParts

/-! Fresh reconstructed end-to-end ratio cell: signed ordinary interpolation
weights, factorial-power normalization, actual binary products, and cleanup. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

def componentBound (w : WordInstance) (q : Recovery.Index w) (answer : ℕ) (B : ℕ) : Prop :=
  RegisterMachine.Bounded B (RatioCombine.registers
    ((-1:ℤ)^(w.particles*Recovery.height w q.1)) (answer:ℤ)
    (interpolationNegativeNumerator (Recovery.degree w) q.1) (interpolationNegativeNumerator (Recovery.innerDegree w q.1) q.2)
    (interpolationDenominator (Recovery.degree w) q.1) (interpolationDenominator (Recovery.innerDegree w q.1) q.2)
    ((q.2.val.factorial:ℤ)^(Recovery.height w q.1)))
noncomputable def costBound (w : WordInstance) (q : Recovery.Index w) (answer B : ℕ) : ℕ :=
  GridWeightsRuntime.pairTime.eval (Recovery.degree w)+GridWeightsRuntime.pairTime.eval (Recovery.innerDegree w q.1)+
  RatioNormalization.time.eval (q.2.val+Recovery.height w q.1+w.particles)+
  5*(signedBits (answer:ℤ)).length+RatioCombine.time.eval B+10

theorem program_executes (g : BitString → ℕ) (w : WordInstance) (q : Recovery.Index w) (answer B : ℕ)
    (hB : componentBound w q answer B) :
    ∃c, program.Executes g
      (state q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
        w.particles (Recovery.height w q.1) (signedBits (answer:ℤ)) [] [] (fields [] [] [] [] [] [] []))
      (state q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
        w.particles (Recovery.height w q.1) (signedBits (answer:ℤ))
        (signedBits (Recovery.ratio w q answer).1) (signedBits (Recovery.ratio w q answer).2)
        (fields [] [] [] [] [] [] [])) c ∧ c≤costBound w q answer B := by
  let nt := signedBits (interpolationNegativeNumerator (Recovery.degree w) q.1)
  let dt := signedBits (interpolationDenominator (Recovery.degree w) q.1)
  let ns := signedBits (interpolationNegativeNumerator (Recovery.innerDegree w q.1) q.2)
  let ds := signedBits (interpolationDenominator (Recovery.innerDegree w q.1) q.2)
  obtain ⟨a,ha,hab⟩ := left_executes g (Recovery.degree w) q.1 q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) (signedBits (answer:ℤ))
  obtain ⟨b,hb,hbb⟩ := right_executes g (Recovery.innerDegree w q.1) q.2 q.1.val (Recovery.degree w-q.1.val)
    w.particles (Recovery.height w q.1) (signedBits (answer:ℤ)) dt nt
  obtain ⟨c,hc,hcb⟩ := norm_executes g q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) (signedBits (answer:ℤ)) dt nt ds ns
  have hd := copyAnswer_executes g q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) (signedBits (answer:ℤ)) dt nt ds ns
    (signedBits ((q.2.val.factorial:ℤ)^(Recovery.height w q.1)))
    (signedBits ((-1:ℤ)^(w.particles*Recovery.height w q.1)))
  obtain ⟨e,he,heb⟩ := combine_executes g q.1.val (Recovery.degree w-q.1.val) q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) (answer:ℤ)
    (interpolationNegativeNumerator (Recovery.degree w) q.1) (interpolationNegativeNumerator (Recovery.innerDegree w q.1) q.2)
    (interpolationDenominator (Recovery.degree w) q.1) (interpolationDenominator (Recovery.innerDegree w q.1) q.2)
    ((q.2.val.factorial:ℤ)^(Recovery.height w q.1)) ((-1:ℤ)^(w.particles*Recovery.height w q.1)) B hB
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc (seq_executes _ _ g hd he))),by unfold costBound;omega⟩

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ GridWeightsRuntime.pairProgram_queryFree)
  (seq_queryFree _ _ (rename_queryFree _ _ GridWeightsRuntime.pairProgram_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ RatioNormalization.program_queryFree)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ RatioCombine.program_queryFree))))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
