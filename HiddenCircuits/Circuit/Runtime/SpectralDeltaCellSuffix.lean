import HiddenCircuits.Circuit.Runtime.SpectralDeltaCellPrepare

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaCell
open Complexity OracleBlock BinaryArithmetic Polynomial SourceSample SourceQueryRecovery

set_option maxHeartbeats 1600000 in
theorem afterCall_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (acc : ℤ×ℤ) (B : ℕ)
    (hB : ∀i,(store (canonical w 0 r.val s.val 0) (SpectralDeltaCell.answered w r s acc) i).length≤B) :
    ∃c,afterCall.Executes g (store (canonical w 0 r.val s.val 0) (SpectralDeltaCell.answered w r s acc))
      (store (canonical w 0 r.val s.val 0) {accumulator:=RationalAccumulator.step acc (SpectralDelta.item w r s)}) c ∧
      c≤afterTime.eval B := by
  let p:=canonical w 0 r.val s.val 0
  let v0:=SpectralDeltaCell.answered w r s acc
  let v1 : Values:={v0 with itemDenominator:=p.firstDenominator}
  let v2 : Values:={v1 with firstNumerator:=signedBits ((SpectralDelta.item w r s).1)}
  let v3 : Values:={v2 with itemDenominator:=signedBits ((SpectralDelta.item w r s).2)}
  let v4 : Values:={v3 with accumulator:=RationalAccumulator.step acc (SpectralDelta.item w r s),firstNumerator:=[],itemDenominator:=[]}
  have h0:=copyDenominator_executes g p v0 rfl
  have hc0 : 5*p.firstDenominator.length+2≤copyTime.eval B := by
    have h:=hB 9
    change p.firstDenominator.length≤B at h
    simp only [copyTime,eval_add,eval_mul,eval_ofNat,eval_X]
    omega
  have hB1 : ∀i,(store p v1 i).length≤numeratorInput.eval B := by
    intro i
    have h:=h0.stack_bound hB i
    change (store p v1 i).length≤B+(5*p.firstDenominator.length+2) at h
    simp only [numeratorInput,eval_add,eval_X]
    omega
  obtain ⟨c1,h1,hb1⟩:=numeratorProduct_executes g p v1
    (spectralWeightData (forbidOccurrences w) 0 r.val).1 (spectralWeightData (signOccurrences w) (-1) s.val).1
    1 1 (SpectralDelta.value w r.val s.val).num
    (numeratorInput.eval B) rfl rfl rfl rfl rfl hB1
  simp only [mul_one] at h1
  change numeratorProduct.Executes g (store p v1) (store p v2) c1 at h1
  have h01:=seq_executes _ _ g h0 h1
  have hB2 : ∀i,(store p v2 i).length≤denominatorInput.eval B := by
    intro i
    have h:=h01.stack_bound hB i
    change (store p v2 i).length≤B+(5*p.firstDenominator.length+2+c1+2) at h
    simp only [denominatorInput,eval_add,eval_comp,eval_X,eval_ofNat]
    omega
  have hfd : p.firstDenominator=signedBits (spectralWeightData (forbidOccurrences w) 0 r.val).2 := by
    change signedBits (SpectralWeights.denominator (forbidOccurrences w))=_
    rw [SpectralWeights.denominator_data (forbidOccurrences w) 0 r.val]
  have hsd : p.secondDenominator=signedBits (spectralWeightData (signOccurrences w) (-1) s.val).2 := by
    change signedBits (SpectralWeights.denominator (signOccurrences w))=_
    rw [SpectralWeights.denominator_data (signOccurrences w) (-1) s.val]
  obtain ⟨c2,h2,hb2⟩:=denominatorProduct_executes g p v2
    (spectralWeightData (forbidOccurrences w) 0 r.val).2 (spectralWeightData (signOccurrences w) (-1) s.val).2
    ((SpectralDelta.value w r.val s.val).den:ℤ) 1
    (denominatorInput.eval B) hfd hsd rfl rfl hB2
  simp only [mul_one] at h2
  change denominatorProduct.Executes g (store p v2) (store p v3) c2 at h2
  have h012:=seq_executes _ _ g h01 h2
  have hB3 : ∀i,(store p v3 i).length≤accumulatorInput.eval B := by
    intro i
    have h:=h2.stack_bound hB2 i
    change (store p v3 i).length≤denominatorInput.eval B+c2 at h
    simp only [accumulatorInput,eval_add,eval_comp,eval_ofNat]
    omega
  obtain ⟨c3,h3,hb3⟩:=accumulate_executes g p v3 (SpectralDelta.item w r s) (accumulatorInput.eval B) rfl rfl hB3
  change accumulate.Executes g (store p v3) (store p v4) c3 at h3
  have hwork := seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 h3))
  have hworkB : 5*p.firstDenominator.length+2+(c1+(c2+c3+2)+2)+2≤afterWorkTime.eval B := by
    simp only [afterWorkTime,eval_add,eval_comp,eval_ofNat]
    omega
  have hB4 : ∀i,(store p v4 i).length≤B+afterWorkTime.eval B := by
    intro i
    exact (hwork.stack_bound hB i).trans (Nat.add_le_add_left hworkB B)
  obtain ⟨c4,h4,hb4⟩:=clearSample_executes g p v4 (B+afterWorkTime.eval B) rfl rfl rfl hB4
  refine ⟨_,seq_executes _ _ g hwork h4,?_⟩
  simp only [afterTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SpectralDeltaCell
