import HiddenCircuits.Circuit.Runtime.DeltaWordRuntime
import HiddenCircuits.Circuit.Runtime.DyadicScalar
import HiddenCircuits.Circuit.Runtime.SourceSampleIntegers

/-! Exact rational recovery for the independent single geometric grid. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaWordRecovery
open HiddenCircuits.Complexity BinaryArithmetic
open scoped BigOperators
abbrev Index {n : ℕ} (w : List (DeltaGate n)) := Fin (2*deltaOccurrences w+1)
def degree {n : ℕ} (w : List (DeltaGate n)) : ℕ := 2*deltaOccurrences w
def word {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) : WordInstance :=
  compileWordInstance hn (w.map (DeltaGate.compileSample u.val)) (zeroBits n) (zeroBits n)
def numerator {n : ℕ} (w : List (DeltaGate n)) (u : Index w) : ℤ :=
  geometricZeroNumerator (degree w) u*DyadicScalar.numerator (DeltaWordEmitter.sampleNegative w false)
def denominator {n : ℕ} (w : List (DeltaGate n)) (u : Index w) : ℤ :=
  geometricBasisDenominator (degree w) u*(2:ℤ)^(DeltaWordEmitter.sampleExponent w u.val)
lemma denominator_ne_zero {n : ℕ} (w : List (DeltaGate n)) (u : Index w) : denominator w u≠0 :=
  mul_ne_zero (geometricBasisDenominator_ne_zero _ _) (pow_ne_zero _ (by norm_num))
lemma coefficient_ratio {n : ℕ} (w : List (DeltaGate n)) (u : Index w) :
    (numerator w u:ℚ)/(denominator w u:ℚ)=
      ((geometricZeroNumerator (degree w) u:ℚ)/(geometricBasisDenominator (degree w) u:ℚ))*
      closedScalar (w.map (DeltaGate.compileSample u.val)) := by
  rw [DeltaWordEmitter.scalar_eq]
  have hd := DyadicScalar.normalization_identity 0 (DeltaWordEmitter.sampleExponent w u.val)
    (DeltaWordEmitter.sampleNegative w false)
  simp only [Nat.mul_zero,Nat.zero_add,pow_zero,one_mul] at hd
  unfold numerator denominator
  push_cast at hd ⊢
  simp only [div_eq_mul_inv,mul_inv_rev] at hd ⊢
  rw [hd]
  ring
lemma geometric_sum {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    (∑u : Index w,(numerator w u:ℚ)*(word hn w u).value/(denominator w u:ℚ))=
      deltaCircuitMatrix w (zeroBits n) (zeroBits n) := by
  have hg := geometricInterpolate_zero_integer_weights (degree w)
    (fun u : Index w=>closedScalar (w.map (DeltaGate.compileSample u.val))*(word hn w u).value)
  have hc := deltaCircuit_from_word_queries hn w (zeroBits n) (zeroBits n)
  change (geometricInterpolate (degree w) (fun u : Index w=>
    closedScalar (w.map (DeltaGate.compileSample u.val))*(word hn w u).value)).eval 0=_ at hc
  rw [hg] at hc
  rw [←hc]
  apply Finset.sum_congr rfl
  intro u _
  calc
    _ = ((numerator w u:ℚ)/(denominator w u:ℚ))*(word hn w u).value := by ring
    _ = _ := by rw [coefficient_ratio];ring
noncomputable def value {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) : ℤ :=
  (word_value_bits_input (word hn w u)).choose
lemma value_cast {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) :
    (word hn w u).value=(value hn w u:ℚ) := (word_value_bits_input (word hn w u)).choose_spec.1
lemma value_length {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) :
    (signedBits (value hn w u)).length≤14*(wordBits (word hn w u)).length^5 := by
  simpa [signedBits,encodeNat_length] using (word_value_bits_input (word hn w u)).choose_spec.2
lemma value_unique {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w)
    (z : ℤ) (hz : (word hn w u).value=(z:ℚ)) : z=value hn w u := by
  exact_mod_cast hz.symm.trans (value_cast hn w u)
def itemOf {n : ℕ} (w : List (DeltaGate n)) (u : Index w) (z : ℤ) : RationalAccumulator.Ratio :=
  (numerator w u*z,denominator w u)
noncomputable def item {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) : RationalAccumulator.Ratio :=
  itemOf w u (value hn w u)
noncomputable def items {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) : List RationalAccumulator.Ratio :=
  List.ofFn (fun u : Index w=>item hn w u)
lemma item_value {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : Index w) :
    RationalAccumulator.value (item hn w u)=
      (numerator w u:ℚ)*(word hn w u).value/(denominator w u:ℚ) := by
  simp only [item,itemOf,RationalAccumulator.value,Int.cast_mul,value_cast]
lemma items_nonzero {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) : ∀b∈items hn w,b.2≠0 := by
  intro b hb
  obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hb
  exact denominator_ne_zero w u
lemma items_value {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) :
    ((items hn w).map RationalAccumulator.value).sum=deltaCircuitMatrix w (zeroBits n) (zeroBits n) := by
  simp only [items,List.map_ofFn,List.sum_ofFn,Function.comp_def,item_value]
  exact geometric_sum hn w
lemma items_length {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) : (items hn w).length=degree w+1 := by
  simp [items,Index,degree]
end HiddenCircuits.Circuit.Runtime.DeltaWordRecovery
