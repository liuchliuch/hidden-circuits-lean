import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterRuntime
import HiddenCircuits.Circuit.Runtime.DeltaAnswerBounds
import HiddenCircuits.Circuit.Runtime.SourceQueryEnumeration

/-! Exact two-dimensional spectral recovery from native Delta oracle answers.
All factors and rational-prefix bounds are derived from the input circuit. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDelta
open Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery
open scoped BigOperators

noncomputable def value {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) : ℚ :=
  (SpectralDeltaEmitter.query w r s).value
noncomputable def item {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) : RationalAccumulator.Ratio :=
  ((spectralWeightData (forbidOccurrences w) 0 r.val).1*(spectralWeightData (signOccurrences w) (-1) s.val).1*(value w r.val s.val).num,
    (spectralWeightData (forbidOccurrences w) 0 r.val).2*(spectralWeightData (signOccurrences w) (-1) s.val).2*((value w r.val s.val).den:ℤ))
noncomputable def row {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) : List RationalAccumulator.Ratio :=
  List.ofFn (fun s : SecondIndex w=>item w r s)
noncomputable def items {n : ℕ} (w : List (ConstraintGate n)) : List RationalAccumulator.Ratio :=
  (List.ofFn (fun r : FirstIndex w=>row w r)).flatten
lemma item_nonzero {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) : (item w r s).2≠0 :=
  mul_ne_zero (mul_ne_zero (spectralWeightData_denominator_ne_zero _ _ _) (spectralWeightData_denominator_ne_zero _ _ _))
    (by exact_mod_cast (value w r.val s.val).den_nz)
lemma item_value {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :
    RationalAccumulator.value (item w r s)=
      targetCoefficient (forbidOccurrences w) 0 r.val*targetCoefficient (signOccurrences w) (-1) s.val*value w r.val s.val := by
  have hf:=spectralWeightData_correct (forbidOccurrences w) 0 r.val
  have hs:=spectralWeightData_correct (signOccurrences w) (-1) s.val
  norm_num only [Int.cast_zero,Int.cast_neg,Int.cast_one] at hf hs
  rw [←hf,←hs,←Rat.num_div_den (value w r.val s.val)]
  simp only [RationalAccumulator.value,item,Int.cast_mul,Int.cast_natCast]
  ring
lemma mem_items {n : ℕ} (w : List (ConstraintGate n)) (b : RationalAccumulator.Ratio) :
    b∈items w ↔ ∃r s,b=item w r s := by
  constructor
  · intro hb
    obtain ⟨xs,hxs,hb⟩:=List.mem_flatten.mp hb
    obtain ⟨r,rfl⟩:=List.mem_ofFn.mp hxs
    obtain ⟨s,hs⟩:=List.mem_ofFn.mp hb
    exact ⟨r,s,hs.symm⟩
  · rintro ⟨r,s,rfl⟩
    exact List.mem_flatten.mpr ⟨row w r,List.mem_ofFn.mpr ⟨r,rfl⟩,List.mem_ofFn.mpr ⟨s,rfl⟩⟩
lemma items_nonzero {n : ℕ} (w : List (ConstraintGate n)) : ∀b∈items w,b.2≠0 := by
  intro b hb;obtain ⟨r,s,rfl⟩:=(mem_items w b).mp hb;exact item_nonzero w r s
lemma items_value {n : ℕ} (w : List (ConstraintGate n)) :
    ((items w).map RationalAccumulator.value).sum=constraintCircuitMatrix w (zeroBits n) (zeroBits n) := by
  simp only [items,row,List.map_flatten,List.map_ofFn,List.sum_flatten,List.sum_ofFn,Function.comp_def,item_value]
  have h:=recover_constraint_circuit w (zeroBits n) (zeroBits n)
  simp_rw [←Fin.sum_univ_eq_sum_range] at h
  exact h

noncomputable def deltaLength : Polynomial ℕ := (1+4*(X+1)^2)*X
noncomputable def answerSize : Polynomial ℕ := (X+4)*deltaLength+2
noncomputable def itemExponent : Polynomial ℕ := 2*SourceQueryBounds.spectralSize+answerSize
noncomputable def countSize : Polynomial ℕ := (X+1)^4
noncomputable def prefixBitSize : Polynomial ℕ := (itemExponent+1)*countSize+itemExponent+2

lemma delta_length_bound {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :
    (sampledConstraintCircuit w r.val s.val).length ≤ deltaLength.eval (circuitBits n w).length := by
  have h:=sampledConstraintCircuit_grid_length w r s
  apply h.trans
  have hm:=polynomial_nat_eval_mono deltaLength (SpectralDeltaEmitter.circuit_size_bounds w).2
  simpa only [deltaLength,eval_mul,eval_add,eval_pow,eval_X,eval_one,eval_ofNat] using hm
lemma answer_bounds {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :
    (value w r.val s.val).num.natAbs ≤ 2^(answerSize.eval (circuitBits n w).length) ∧
    ((value w r.val s.val).den:ℤ).natAbs ≤ 2^(answerSize.eval (circuitBits n w).length) := by
  have hn:=(SpectralDeltaEmitter.circuit_size_bounds w).1
  have hl:=delta_length_bound w r s
  have hu:=DeltaValues.numerator_length (sampledConstraintCircuit w r.val s.val) (zeroBits n) (zeroBits n)
  have hv:=DeltaValues.denominator_length (sampledConstraintCircuit w r.val s.val) (zeroBits n) (zeroBits n)
  have hm:=Nat.mul_le_mul (Nat.add_le_add_right hn 4) hl
  constructor
  · apply abs_le_pow_signed_length
    change (signedBits (deltaCircuitMatrix (sampledConstraintCircuit w r.val s.val) (zeroBits n) (zeroBits n)).num).length ≤ _
    simp only [answerSize,eval_add,eval_mul,eval_X,eval_ofNat]
    omega
  · apply abs_le_pow_signed_length
    change (signedBits ((deltaCircuitMatrix (sampledConstraintCircuit w r.val s.val) (zeroBits n) (zeroBits n)).den:ℤ)).length ≤ _
    simp only [answerSize,eval_add,eval_mul,eval_X,eval_ofNat]
    nlinarith
lemma item_bounds {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :
    (item w r s).1.natAbs ≤ 2^(itemExponent.eval (circuitBits n w).length) ∧
    (item w r s).2.natAbs ≤ 2^(itemExponent.eval (circuitBits n w).length) := by
  have h:=SourceQueryBounds.spectral_factor_bounds w 0 r.val s.val
  simp only [Nat.add_zero] at h
  have ha:=answer_bounds w r s
  constructor
  · simpa only [item,Int.natAbs_mul,itemExponent,eval_add,eval_mul,eval_ofNat,two_mul,pow_add] using
      Nat.mul_le_mul (Nat.mul_le_mul h.1 h.2.1) ha.1
  · simpa only [item,Int.natAbs_mul,itemExponent,eval_add,eval_mul,eval_ofNat,two_mul,pow_add] using
      Nat.mul_le_mul (Nat.mul_le_mul h.2.2.1 h.2.2.2) ha.2
lemma items_length_bound {n : ℕ} (w : List (ConstraintGate n)) :
    (items w).length ≤ countSize.eval (circuitBits n w).length := by
  have h:=SourceQueryEnumeration.spectral_count_bounds w 0
  simp only [Nat.add_zero,FirstIndex,SecondIndex,Fintype.card_fin] at h
  have he : (items w).length=Fintype.card (FirstIndex w)*Fintype.card (SecondIndex w) := by simp [items,row,Function.comp_def,List.sum_ofFn]
  rw [he]
  have hm:=Nat.mul_le_mul h.1 h.2
  simpa only [FirstIndex,SecondIndex,Fintype.card_fin,countSize,eval_pow,eval_add,eval_mul,eval_X,eval_one,show 4=2+2 from rfl,pow_add] using hm
lemma bitBound {n : ℕ} (w : List (ConstraintGate n)) (acc : RationalAccumulator.Ratio) (A : ℕ)
    (ha : acc.1.natAbs ≤ 2^A ∧ acc.2.natAbs ≤ 2^A) :
    RationalAccumulator.BitBound (A+prefixBitSize.eval (circuitBits n w).length) acc (items w) := by
  have hall : ∀b∈items w,b.1.natAbs ≤ 2^(itemExponent.eval (circuitBits n w).length) ∧ b.2.natAbs ≤ 2^(itemExponent.eval (circuitBits n w).length) := by
    intro b hb;obtain ⟨r,s,rfl⟩:=(mem_items w b).mp hb;exact item_bounds w r s
  apply (RationalAccumulator.bitBound_of_abs acc (items w) A (itemExponent.eval (circuitBits n w).length) ha hall).mono
  have hm:=Nat.mul_le_mul_left (itemExponent.eval (circuitBits n w).length+1) (items_length_bound w)
  simp only [prefixBitSize,eval_add,eval_mul,eval_one,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SpectralDelta
