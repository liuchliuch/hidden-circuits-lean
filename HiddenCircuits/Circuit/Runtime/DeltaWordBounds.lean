import HiddenCircuits.Circuit.Runtime.DeltaWordSampleProgram
import HiddenCircuits.Circuit.SampleBounds

/-! Polynomial query, answer, and every unreduced accumulator prefix bound in
literal input bytes for the single Delta interpolation grid. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaWordBounds
open HiddenCircuits.Complexity BinaryArithmetic Polynomial DeltaWordRecovery
noncomputable def inputSize : Polynomial ℕ := 3*X
noncomputable def wordSize : Polynomial ℕ := inputSize+DeltaWordEmitter.emitTime.comp inputSize
noncomputable def geometricSize : Polynomial ℕ := (2*X+1)^2+2
noncomputable def resultSize : Polynomial ℕ := 14*wordSize^5
noncomputable def itemExponent : Polynomial ℕ := geometricSize+wordSize+resultSize
noncomputable def prefixBitSize : Polynomial ℕ := (itemExponent+1)*(2*X+1)+itemExponent+2
noncomputable def storageSize : Polynomial ℕ := 3*X+2
lemma degree_bound {n : ℕ} (w : List (DeltaGate n)) : degree w≤2*(DeltaWordEmitter.circuitBits n w).length := by
  have h:=deltaOccurrences_le_length w
  have hl:=(DeltaWordEmitter.circuit_size_bounds w).2
  unfold DeltaWordRecovery.degree;omega
lemma sample_input_bound {n : ℕ} (w : List (DeltaGate n)) (u : Index w) :
    DeltaWordEmitter.inputSize w 0 0 u.val≤ inputSize.eval (DeltaWordEmitter.circuitBits n w).length := by
  have hd:=degree_bound w
  have hu : u.val<degree w+1:=u.isLt
  simp only [DeltaWordEmitter.inputSize,inputSize,eval_mul,eval_ofNat,eval_X];omega
lemma emission_bounds {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) :
    (wordBits (word hn w u)).length≤wordSize.eval (DeltaWordEmitter.circuitBits n w).length ∧
      DeltaWordEmitter.sampleExponent w u.val≤wordSize.eval (DeltaWordEmitter.circuitBits n w).length := by
  have h:=DeltaWordEmitter.emitted_length_bound (fun _=>0) w 0 0 u.val
  rw [DeltaWordEmitter.rawBits_eq_wordBits hn] at h
  have hb:=sample_input_bound w u
  have hm:=polynomial_nat_eval_mono DeltaWordEmitter.emitTime hb
  dsimp only at hm
  simp only [wordSize,eval_add,eval_comp]
  exact ⟨h.1.trans (Nat.add_le_add hb hm),h.2.trans (Nat.add_le_add hb hm)⟩
lemma geometric_bounds {n : ℕ} (w : List (DeltaGate n)) (u : Index w) :
    (geometricZeroNumerator (degree w) u).natAbs≤2^(geometricSize.eval (DeltaWordEmitter.circuitBits n w).length) ∧
    (geometricBasisDenominator (degree w) u).natAbs≤2^(geometricSize.eval (DeltaWordEmitter.circuitBits n w).length) := by
  have hg:=geometricZeroWeights_bits (degree w) u
  have hd:=degree_bound w
  have he : (degree w+1)^2+2≤geometricSize.eval (DeltaWordEmitter.circuitBits n w).length := by
    simp only [geometricSize,eval_add,eval_pow,eval_mul,eval_X,eval_ofNat,eval_one]
    gcongr
  exact ⟨(Nat.size_le.mp (by omega : _≤geometricSize.eval (DeltaWordEmitter.circuitBits n w).length)).le,
    (Nat.size_le.mp (by omega : _≤geometricSize.eval (DeltaWordEmitter.circuitBits n w).length)).le⟩
lemma result_bound {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) :
    (value hn w u).natAbs≤2^(resultSize.eval (DeltaWordEmitter.circuitBits n w).length) := by
  have h:=value_length hn w u
  simp only [signedBits,encodeNat_length,List.length_cons] at h
  have hm:=Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left (emission_bounds hn w u).1 5)
  apply (Nat.size_le.mp (Nat.le_trans (Nat.le_succ _) h)).le.trans
  apply Nat.pow_le_pow_right (by decide)
  simpa only [resultSize,eval_mul,eval_ofNat,eval_pow] using hm
lemma numerator_bound {n : ℕ} (w : List (DeltaGate n)) (u : Index w) :
    (numerator w u).natAbs≤2^(geometricSize.eval (DeltaWordEmitter.circuitBits n w).length) := by
  have hsign : (DyadicScalar.numerator (DeltaWordEmitter.sampleNegative w false)).natAbs=1 := by
    unfold DyadicScalar.numerator;split_ifs <;> rfl
  simpa only [numerator,Int.natAbs_mul,hsign,Nat.mul_one] using (geometric_bounds w u).1
lemma denominator_bound {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) :
    (denominator w u).natAbs≤2^((geometricSize+wordSize).eval (DeltaWordEmitter.circuitBits n w).length) := by
  have he : ((2:ℤ)^(DeltaWordEmitter.sampleExponent w u.val)).natAbs≤2^(wordSize.eval (DeltaWordEmitter.circuitBits n w).length) := by
    simpa only [Int.natAbs_pow,show (2:ℤ).natAbs=2 from rfl] using
      Nat.pow_le_pow_right (show 0<2 by decide) (emission_bounds hn w u).2
  simpa only [denominator,Int.natAbs_mul,eval_add,pow_add] using Nat.mul_le_mul (geometric_bounds w u).2 he
lemma item_bound {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) :
    (item hn w u).1.natAbs≤2^(itemExponent.eval (DeltaWordEmitter.circuitBits n w).length) ∧
    (item hn w u).2.natAbs≤2^(itemExponent.eval (DeltaWordEmitter.circuitBits n w).length) := by
  constructor
  · simp only [item,itemOf,Int.natAbs_mul]
    have h:=Nat.mul_le_mul (numerator_bound w u) (result_bound hn w u)
    simp only [←pow_add] at h
    apply h.trans
    apply Nat.pow_le_pow_right (by decide)
    simp only [itemExponent,eval_add];omega
  · apply (denominator_bound hn w u).trans
    apply Nat.pow_le_pow_right (by decide)
    simp only [itemExponent,eval_add];omega
lemma bitBound {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    RationalAccumulator.BitBound (prefixBitSize.eval (DeltaWordEmitter.circuitBits n w).length) (0,1) (items hn w) := by
  apply (RationalAccumulator.bitBound_of_abs (0,1) (items hn w) 0
    (itemExponent.eval (DeltaWordEmitter.circuitBits n w).length) (by decide) (by
      intro b hb;obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hb;exact item_bound hn w u)).mono
  have hd:=degree_bound w
  have hm:=Nat.mul_le_mul_left (itemExponent.eval (DeltaWordEmitter.circuitBits n w).length+1) (Nat.add_le_add_right hd 1)
  rw [items_length]
  simp only [prefixBitSize,eval_add,eval_mul,eval_X,eval_ofNat,eval_one];omega
set_option maxHeartbeats 1000000 in
lemma state_bound {n : ℕ} (w : List (DeltaGate n)) (u : Index w) (C : ℕ) (acc : RationalAccumulator.Ratio)
    (ha : RationalAccumulator.Bounded C acc) :
    ∀i,(SourceSample.store (DeltaWordSample.canonical w u.val) {accumulator:=acc,degree:=degree w} i).length≤
      storageSize.eval ((DeltaWordEmitter.circuitBits n w).length+C) := by
  have hd:=degree_bound w
  have hu : u.val<degree w+1:=u.isLt
  rcases ha with ⟨ha1,ha2⟩
  have hz : (signedBits 0).length=1:=rfl
  have ho : (signedBits 1).length=2:=rfl
  intro i
  fin_cases i <;> simp [SourceSample.store,DeltaWordSample.canonical,storageSize] <;> omega
end HiddenCircuits.Circuit.Runtime.DeltaWordBounds
