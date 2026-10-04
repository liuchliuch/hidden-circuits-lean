import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorBounds

/-! Unconditional polynomial runtime for the actual signed list folds. All
intermediate bounds are derived from the canonical serialized input length. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic

/-- Length of the two physical input words, including signs and delimiters. -/
def operandStreamLength (a : ℤ) (zs : List ℤ) : ℕ :=
  (signedBits a).length+(encodeBitList (zs.map signedBits)).length

lemma member_length_le_encodeBitList {x : BitString} {xs : List BitString} (h : x∈xs) :
    x.length≤(encodeBitList xs).length := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    simp only [encodeBitList,List.length_cons,pairBits_length]
    rcases h with rfl|h
    · omega
    · have := ih h; omega

lemma stream_list_length (a : ℤ) (zs : List ℤ) : zs.length≤operandStreamLength a zs := by
  have h := list_length_le_encodeBitList_length (zs.map signedBits)
  simp only [List.length_map] at h
  unfold operandStreamLength
  omega

lemma stream_head_length (a : ℤ) (zs : List ℤ) : (signedBits a).length≤operandStreamLength a zs := by
  unfold operandStreamLength; omega

lemma stream_member_length (a z : ℤ) (zs : List ℤ) (hz : z∈zs) :
    (signedBits z).length≤operandStreamLength a zs := by
  have h := member_length_le_encodeBitList (List.mem_map.mpr ⟨z,hz,rfl⟩ : signedBits z∈zs.map signedBits)
  unfold operandStreamLength; omega

lemma abs_le_pow_signed_length (z : ℤ) (N : ℕ) (h : (signedBits z).length≤N) : z.natAbs≤2^N := by
  have hv := value_lt_pow_length (Computability.encodeNat z.natAbs)
  rw [value_encodeNat] at hv
  apply hv.le.trans
  apply Nat.pow_le_pow_right (by decide)
  simp only [signedBits,List.length_cons] at h
  omega

/-- Uniform quadratic envelope for every partial product, derived from actual
encoded input lengths without any intermediate-value assumption. -/
theorem productBitBound_stream (a : ℤ) (zs : List ℤ) :
    ProductBitBound ((operandStreamLength a zs)^2+operandStreamLength a zs+2) a zs := by
  let N := operandStreamLength a zs
  have hN := stream_list_length a zs
  have ha := abs_le_pow_signed_length a N (stream_head_length a zs)
  have hz (z : ℤ) (h : z∈zs) := abs_le_pow_signed_length z N (stream_member_length a z zs h)
  have hp := productBitBound_of_abs N N a zs ha hz
  apply hp.mono
  have hm := Nat.mul_le_mul_left N hN
  dsimp [N] at *
  nlinarith

/-- Uniform quadratic envelope for every partial sum. -/
theorem sumBitBound_stream (a : ℤ) (zs : List ℤ) :
    SumBitBound ((operandStreamLength a zs)^2+2*operandStreamLength a zs+2) a zs := by
  let N := operandStreamLength a zs
  have hN := stream_list_length a zs
  have ha := abs_le_pow_signed_length a N (stream_head_length a zs)
  have hz (z : ℤ) (h : z∈zs) := abs_le_pow_signed_length z N (stream_member_length a z zs h)
  have hp := sumBitBound_of_abs N N a zs ha hz
  apply hp.mono
  have hm := Nat.mul_le_mul_left (N+1) hN
  dsimp [N] at *
  nlinarith

noncomputable def productAccumulatorTime : Polynomial ℕ :=
  1+Polynomial.X*(50*(2*(Polynomial.X^2+Polynomial.X+2)+1)^3+
    10*(Polynomial.X^2+Polynomial.X+2)+20)

noncomputable def sumAccumulatorTime : Polynomial ℕ :=
  1+Polynomial.X*(500*(Polynomial.X^2+2*Polynomial.X+3))

/-- A fixed finite bit-stack product algorithm, with an unconditional degree
seven polynomial in the complete serialized input length. -/
theorem productAccumulator_polynomial (g : BitString → ℕ) (zs : List ℤ) (a : ℤ) :
    ∃ t, productAccumulator.Executes g
      (productStore (signedBits a) [] [] [] [] [] (encodeBitList (zs.map signedBits)))
      (productStore (signedBits (a*zs.prod)) [] [] [] [] [] []) t ∧
      t≤productAccumulatorTime.eval (operandStreamLength a zs) := by
  obtain ⟨t,ht,hb⟩ := productAccumulator_executes g zs a _ (productBitBound_stream a zs)
  refine ⟨t,by simpa [foldl_mul_eq] using ht,?_⟩
  apply hb.trans
  simp only [productAccumulatorTime,Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_ofNat,productIterationBound]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (stream_list_length a zs)) 1

/-- A fixed finite bit-stack sum algorithm, with an unconditional cubic
polynomial in the complete serialized input length. -/
theorem sumAccumulator_polynomial (g : BitString → ℕ) (zs : List ℤ) (a : ℤ) :
    ∃ t, sumAccumulator.Executes g
      (sumStore (signedBits a) [] [] [] (encodeBitList (zs.map signedBits)))
      (sumStore (signedBits (a+zs.sum)) [] [] [] []) t ∧
      t≤sumAccumulatorTime.eval (operandStreamLength a zs) := by
  obtain ⟨t,ht,hb⟩ := sumAccumulator_executes g zs a _ (sumBitBound_stream a zs)
  refine ⟨t,by simpa [foldl_add_eq] using ht,?_⟩
  apply hb.trans
  simp only [sumAccumulatorTime,Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_ofNat,sumIterationBound]
  convert Nat.add_le_add_left
    (Nat.mul_le_mul_right (500*((operandStreamLength a zs)^2+2*operandStreamLength a zs+3))
      (stream_list_length a zs)) 1 using 1 <;> congr 1 <;> ring

end HiddenCircuits.Complexity.BinaryArithmetic
