import HiddenCircuits.Circuit.Runtime.SourceQueryBounds

/-! Cardinality and every rational prefix of the
actual nested source query list, derived from its factors, not certificates. -/
namespace HiddenCircuits.Circuit.Runtime.SourceQueryEnumeration
open HiddenCircuits.Complexity BinaryArithmetic Polynomial SourceQueryRecovery
open SourceSampleIntegers SourceQueryBounds
open scoped BigOperators

lemma flatten_length_bound {α : Type*} (xs : List (List α)) (B : ℕ)
    (h : ∀x∈xs,x.length≤B) : xs.flatten.length≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=h x (by simp)
    have ht:=ih (by intro y hy;exact h y (by simp [hy]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
lemma spectral_count_bounds {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) :
    Fintype.card (FirstIndex w)≤((circuitBits n w).length+a+1)^2 ∧
    Fintype.card (SecondIndex w)≤((circuitBits n w).length+a+1)^2 := by
  simpa only [FirstIndex,SecondIndex,Fintype.card_fin] using And.intro
    ((spectralIndex_card_bound (forbidOccurrences w)).trans (Nat.pow_le_pow_left (Nat.add_le_add_right (occurrence_bounds w a).1 1) 2))
    ((spectralIndex_card_bound (signOccurrences w)).trans (Nat.pow_le_pow_left (Nat.add_le_add_right (occurrence_bounds w a).2 1) 2))
lemma row_length_bound {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) :
    (rowItems hn a w r s).length≤degreeSize.eval ((circuitBits n w).length+a)+1 := by
  simpa only [rowItems,List.length_ofFn,ThirdIndex,SourceQueryRecovery.degree] using Nat.add_le_add_right (degree_bound w a r s) 1
lemma middle_length_bound {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) (r : FirstIndex w) :
    (middleItems hn a w r).length≤((circuitBits n w).length+a+1)^2*(degreeSize.eval ((circuitBits n w).length+a)+1) := by
  have h:=flatten_length_bound (List.ofFn (fun s : SecondIndex w => rowItems hn a w r s)) _ (by
    intro x hx;obtain ⟨s,rfl⟩:=List.mem_ofFn.mp hx;exact row_length_bound hn a w r s)
  apply h.trans
  simpa only [List.length_ofFn,Fintype.card_fin] using Nat.mul_le_mul_right _ (spectral_count_bounds w a).2
lemma items_length_bound {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) :
    (items hn a w).length≤countSize.eval ((circuitBits n w).length+a) := by
  let L := (circuitBits n w).length+a
  have h:=flatten_length_bound (List.ofFn (fun r : FirstIndex w => middleItems hn a w r)) _ (by
    intro x hx;obtain ⟨r,rfl⟩:=List.mem_ofFn.mp hx;exact middle_length_bound hn a w r)
  have hc:=(spectral_count_bounds w a).1
  have hm:=Nat.mul_le_mul_right ((L+1)^2*(degreeSize.eval L+1)) hc
  simp only [FirstIndex,Fintype.card_fin] at hm
  simp only [List.length_ofFn] at h
  have ht := h.trans hm
  change (items hn a w).length≤(L+1)^2*((L+1)^2*(degreeSize.eval L+1)) at ht
  apply ht.trans
  simp only [countSize,degreeSize,eval_mul,eval_pow,eval_add,eval_ofNat,eval_X,eval_one]
  change (L+1)^2*((L+1)^2*(8*(L+1)^3+1))≤9*(L+1)^7
  have hp : (L+1)^4≤(L+1)^7 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith [show (L+1)^2*((L+1)^2*(8*(L+1)^3+1))=8*(L+1)^7+(L+1)^4 by ring]
lemma items_bound {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) :
    ∀b∈items hn a w,b.1.natAbs≤2^(itemExponent.eval ((circuitBits n w).length+a)) ∧
      b.2.natAbs≤2^(itemExponent.eval ((circuitBits n w).length+a)) := by
  intro b hb
  obtain ⟨r,s,u,rfl⟩ := (mem_items hn a w b).mp hb
  exact ratio_bound hn a w r s u

noncomputable def accumulatorExponent : Polynomial ℕ := (itemExponent+1)*countSize
noncomputable def prefixBitSize : Polynomial ℕ := accumulatorExponent+itemExponent+2

lemma run_abs_bound (acc : RationalAccumulator.Ratio) (xs : List RationalAccumulator.Ratio) (A E : ℕ)
    (ha : acc.1.natAbs≤2^A ∧ acc.2.natAbs≤2^A)
    (hs : ∀b∈xs,b.1.natAbs≤2^E ∧ b.2.natAbs≤2^E) :
    (RationalAccumulator.run acc xs).1.natAbs≤2^(A+(E+1)*xs.length) ∧
    (RationalAccumulator.run acc xs).2.natAbs≤2^(A+(E+1)*xs.length) := by
  induction xs generalizing acc A with
  | nil => simpa using ha
  | cons b xs ih =>
    have hb:=hs b (by simp)
    have ht:=ih (RationalAccumulator.step acc b) (A+E+1) (RationalAccumulator.step_abs_bound ha hb)
      (by intro z hz;exact hs z (by simp [hz]))
    have he : A+(E+1)*(b::xs).length=(A+E+1)+(E+1)*xs.length := by simp only [List.length_cons];ring
    rw [RationalAccumulator.run_cons,he]
    exact ht
lemma prefix_abs_bound {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (acc : RationalAccumulator.Ratio) (A j : ℕ) (ha : acc.1.natAbs≤2^A ∧ acc.2.natAbs≤2^A) :
    (RationalAccumulator.run acc ((items hn a w).take j)).1.natAbs≤2^(A+accumulatorExponent.eval ((circuitBits n w).length+a)) ∧
    (RationalAccumulator.run acc ((items hn a w).take j)).2.natAbs≤2^(A+accumulatorExponent.eval ((circuitBits n w).length+a)) := by
  have h:=run_abs_bound acc ((items hn a w).take j) A (itemExponent.eval ((circuitBits n w).length+a)) ha
    (by intro b hb;exact items_bound hn a w b (List.mem_of_mem_take hb))
  have hlen : ((items hn a w).take j).length≤countSize.eval ((circuitBits n w).length+a) := by
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans (items_length_bound hn a w)
  have hp : 2^(A+(itemExponent.eval ((circuitBits n w).length+a)+1)*((items hn a w).take j).length)≤
      2^(A+accumulatorExponent.eval ((circuitBits n w).length+a)) := by
    apply Nat.pow_le_pow_right (by decide)
    simpa only [accumulatorExponent,eval_mul,eval_add,eval_one] using
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) A
  exact ⟨h.1.trans hp,h.2.trans hp⟩
lemma bitBound {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (acc : RationalAccumulator.Ratio) (A : ℕ) (ha : acc.1.natAbs≤2^A ∧ acc.2.natAbs≤2^A) :
    RationalAccumulator.BitBound (A+prefixBitSize.eval ((circuitBits n w).length+a)) acc (items hn a w) := by
  apply (RationalAccumulator.bitBound_of_abs acc (items hn a w) A _ ha (items_bound hn a w)).mono
  have hm:=Nat.mul_le_mul_left (itemExponent.eval ((circuitBits n w).length+a)+1) (items_length_bound hn a w)
  simp only [prefixBitSize,accumulatorExponent,eval_add,eval_mul,eval_one,eval_ofNat]
  omega
lemma source_bitBound {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    RationalAccumulator.BitBound ((prefixBitSize.comp sourceInputSize).eval (GraphInput.encode ⟨n,G⟩).length)
      (0,1) (items hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates) := by
  have h:=bitBound hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates (0,1) 0 (by decide)
  simp only [Nat.zero_add] at h
  apply h.mono
  simpa only [eval_comp] using polynomial_nat_eval_mono prefixBitSize (source_input_bound G)
lemma indices_length_bound {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) :
    (indices w).length≤countSize.eval ((circuitBits n w).length+a) := by
  have h:=items_length_bound hn a w
  rw [items_eq_map_indices,List.length_map] at h
  exact h
lemma source_items_length {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    (items hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates).length≤
      (countSize.comp sourceInputSize).eval (GraphInput.encode ⟨n,G⟩).length := by
  apply (items_length_bound hn _ _).trans
  simpa only [eval_comp] using polynomial_nat_eval_mono countSize (source_input_bound G)
end HiddenCircuits.Circuit.Runtime.SourceQueryEnumeration
