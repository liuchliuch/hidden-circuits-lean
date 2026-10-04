import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryBounds
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCombine

/-! Reconstructed input-register bounds for the actual five-multiplication cell. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Recovery
open Complexity BinaryArithmetic

theorem ratio_registers_bounded (w : WordInstance) (hw : w.word≠[]) (q : Index w) :
    RegisterMachine.Bounded (termExponent (wordBits w).length+2)
      (RatioCombine.registers ((-1:ℤ)^(w.particles*height w q.1))
        (perfectMatchingCount (query w q).2.graph:ℤ)
        (interpolationNegativeNumerator (degree w) q.1)
        (interpolationNegativeNumerator (innerDegree w q.1) q.2)
        (interpolationDenominator (degree w) q.1)
        (interpolationDenominator (innerDegree w q.1) q.2)
        ((q.2.val.factorial:ℤ)^(height w q.1))) := by
  let L := (wordBits w).length
  have ho := weights_envelope q.1 (parameter_bounds w q.1).1
  have hi := weights_envelope q.2 (parameter_bounds w q.1).2.2
  have hn := normalization_envelope w q
  have ha := query_answer_bound w hw q
  have hE : (innerBound L)^2+1 ≤ termExponent L := by unfold termExponent;omega
  have hD : (outerBound L)^2+1 ≤ termExponent L := by unfold termExponent;omega
  have hA : (vertexBound L+1)^2 ≤ termExponent L := by unfold termExponent;omega
  have hN : (innerBound L)^2*heightBound L ≤ termExponent L := by unfold termExponent;omega
  have hsign : ((-1:ℤ)^(w.particles*height w q.1)).natAbs ≤ 2^(termExponent L) := by
    simp only [Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,one_pow]
    exact Nat.one_le_pow _ _ (by decide)
  have hnb := hn.trans (Nat.pow_le_pow_right (by decide) hN)
  have hab := ha.trans (Nat.pow_le_pow_right (by decide) hA)
  have hnt := ho.1.trans (Nat.pow_le_pow_right (by decide) hD)
  have hdt := ho.2.trans (Nat.pow_le_pow_right (by decide) hD)
  have hns := hi.1.trans (Nat.pow_le_pow_right (by decide) hE)
  have hds := hi.2.trans (Nat.pow_le_pow_right (by decide) hE)
  intro i
  apply signedBits_length_of_abs_bound
  fin_cases i <;> dsimp only [RatioCombine.registers]
  · exact hsign
  · exact hab
  · exact hnt
  · exact hns
  · exact hdt
  · exact hds
  · exact hnb
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Recovery
