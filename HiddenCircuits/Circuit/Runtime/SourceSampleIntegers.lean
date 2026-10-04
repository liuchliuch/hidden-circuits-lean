import HiddenCircuits.Circuit.Runtime.SourceQueryRecovery
import HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator

/-! The actual signed integer returned by each
canonical sample word, and the literal lexicographic nested query list. -/
namespace HiddenCircuits.Circuit.Runtime.SourceSampleIntegers
open HiddenCircuits.Complexity BinaryArithmetic SourceQueryRecovery
open scoped BigOperators

noncomputable def value {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) : ℤ :=
  (word_value_bits_input (word hn w r s u)).choose
lemma value_cast {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (word hn w r s u).value=(value hn w r s u:ℚ) :=
  (word_value_bits_input (word hn w r s u)).choose_spec.1
lemma value_length {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (signedBits (value hn w r s u)).length≤14*(wordBits (word hn w r s u)).length^5 := by
  simpa [signedBits,encodeNat_length] using (word_value_bits_input (word hn w r s u)).choose_spec.2
lemma value_size {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (value hn w r s u).natAbs.size+1≤14*(wordBits (word hn w r s u)).length^5 :=
  (word_value_bits_input (word hn w r s u)).choose_spec.2
lemma value_unique {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s)
    (z : ℤ) (hz : (word hn w r s u).value=(z:ℚ)) : z=value hn w r s u := by
  exact_mod_cast hz.symm.trans (value_cast hn w r s u)

noncomputable def item {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) : RationalAccumulator.Ratio :=
  (numerator w r s u*value hn w r s u,denominator a w r s u)
def indices {n : ℕ} (w : List (ConstraintGate n)) : List (QueryIndex w) :=
  (List.ofFn (fun r : FirstIndex w =>
    (List.ofFn (fun s : SecondIndex w =>
      List.ofFn (fun u : ThirdIndex w r s => (⟨r,s,u⟩ : QueryIndex w)))).flatten)).flatten
noncomputable def rowItems {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) : List RationalAccumulator.Ratio :=
  List.ofFn (fun u : ThirdIndex w r s => item hn a w r s u)
noncomputable def middleItems {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) : List RationalAccumulator.Ratio :=
  (List.ofFn (fun s : SecondIndex w => rowItems hn a w r s)).flatten
noncomputable def items {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) : List RationalAccumulator.Ratio :=
  (List.ofFn (fun r : FirstIndex w => middleItems hn a w r)).flatten
lemma item_nonzero {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (item hn a w r s u).2≠0 := denominator_ne_zero a w r s u
lemma item_value {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    RationalAccumulator.value (item hn a w r s u)=
      (numerator w r s u:ℚ)*(word hn w r s u).value/(denominator a w r s u:ℚ) := by
  exact term_of_signed_result hn a w r s u _ (value_cast hn w r s u)
lemma mem_items {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) (b : RationalAccumulator.Ratio) :
    b∈items hn a w ↔ ∃r s u,b=item hn a w r s u := by
  constructor
  · intro hb
    obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
    obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hbs
    obtain ⟨cs,hcs,hb⟩ := List.mem_flatten.mp hb
    obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hcs
    obtain ⟨u,hu⟩ := List.mem_ofFn.mp hb
    exact ⟨r,s,u,hu.symm⟩
  · rintro ⟨r,s,u,rfl⟩
    apply List.mem_flatten.mpr
    refine ⟨middleItems hn a w r,List.mem_ofFn.mpr ⟨r,rfl⟩,?_⟩
    apply List.mem_flatten.mpr
    exact ⟨rowItems hn a w r s,List.mem_ofFn.mpr ⟨s,rfl⟩,List.mem_ofFn.mpr ⟨u,rfl⟩⟩

lemma items_nonzero {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) :
    ∀b∈items hn a w,b.2≠0 := by
  intro b hb
  obtain ⟨r,s,u,rfl⟩ := (mem_items hn a w b).mp hb
  exact item_nonzero hn a w r s u
lemma items_value {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) :
    ((items hn a w).map RationalAccumulator.value).sum=
      (1/8:ℚ)^a*constraintCircuitMatrix w (zeroBits n) (zeroBits n) := by
  simp only [items,middleItems,rowItems,List.map_flatten,List.map_ofFn,
    List.sum_flatten,List.sum_ofFn,Function.comp_def,item_value]
  exact triple_sum hn a w
lemma restoring_run_value {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    RationalAccumulator.value (RationalAccumulator.run (0,1)
      (items hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates))=(G.independentCount:ℚ) := by
  rw [RationalAccumulator.run_value _ _ (by decide) (items_nonzero _ _ _),items_value]
  simp only [RationalAccumulator.value,Int.cast_zero,Int.cast_one,zero_div,zero_add]
  rw [←restoringIndependentProgram_scalar]
  exact restoringIndependentProgram_correct G
lemma restoring_run_nonzero {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    (RationalAccumulator.run (0,1)
      (items hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates)).2≠0 :=
  RationalAccumulator.run_nonzero _ _ (by decide) (items_nonzero _ _ _)
lemma items_eq_map_indices {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) :
    items hn a w=(indices w).map (fun q => item hn a w q.1 q.2.1 q.2.2) := by
  simp only [indices,items,middleItems,rowItems,List.map_flatten,List.map_ofFn,Function.comp_def]
lemma restoring_run_division {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    let acc := RationalAccumulator.run (0,1)
      (items hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates)
    acc.2 ∣ acc.1 ∧ acc.1/acc.2=(G.independentCount:ℤ) := by
  dsimp only
  let acc := RationalAccumulator.run (0,1)
    (items hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates)
  have hb : acc.2≠0 := restoring_run_nonzero hn G
  have hbq : (acc.2:ℚ)≠0 := by exact_mod_cast hb
  have hv : (acc.1:ℚ)/(acc.2:ℚ)=(G.independentCount:ℚ) := restoring_run_value hn G
  have he : acc.1=(G.independentCount:ℤ)*acc.2 := by exact_mod_cast (div_eq_iff hbq).mp hv
  constructor
  · exact ⟨G.independentCount,by rw [he];ring⟩
  · change acc.1/acc.2=(G.independentCount:ℤ)
    rw [he]
    exact Int.mul_ediv_cancel _ hb
end HiddenCircuits.Circuit.Runtime.SourceSampleIntegers
