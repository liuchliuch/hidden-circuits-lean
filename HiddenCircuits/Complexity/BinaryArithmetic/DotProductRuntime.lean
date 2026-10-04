import HiddenCircuits.Complexity.BinaryArithmetic.DotProduct

/-! Unconditional serialized-input polynomial bound for the finite dot product. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic

def dotStreamLength (acc : ℤ) (ps : List (ℤ×ℤ)) : ℕ := (signedBits acc).length+
  (encodeBitList (ps.map (fun p => signedBits p.1))).length+
  (encodeBitList (ps.map (fun p => signedBits p.2))).length

lemma dot_list_length (acc : ℤ) (ps : List (ℤ×ℤ)) : ps.length≤dotStreamLength acc ps := by
  have h := list_length_le_encodeBitList_length (ps.map (fun p => signedBits p.1))
  simp only [List.length_map] at h
  unfold dotStreamLength
  omega

lemma dot_pair_length (acc : ℤ) (ps : List (ℤ×ℤ)) (p : ℤ×ℤ) (hp : p∈ps) :
    (signedBits p.1).length≤dotStreamLength acc ps ∧ (signedBits p.2).length≤dotStreamLength acc ps := by
  have h₁ := member_length_le_encodeBitList
    (List.mem_map.mpr ⟨p,hp,rfl⟩ : signedBits p.1∈ps.map (fun p => signedBits p.1))
  have h₂ := member_length_le_encodeBitList
    (List.mem_map.mpr ⟨p,hp,rfl⟩ : signedBits p.2∈ps.map (fun p => signedBits p.2))
  unfold dotStreamLength
  omega

lemma dotBitBound_of_sum {B : ℕ} (acc : ℤ) (ps : List (ℤ×ℤ))
    (hs : SumBitBound B acc (ps.map (fun p => p.1*p.2)))
    (hi : ∀ p∈ps, (signedBits p.1).length≤B ∧ (signedBits p.2).length≤B) :
    DotBitBound B acc ps := by
  induction ps generalizing acc with
  | nil => exact hs
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    obtain ⟨hacc,hprod,htail⟩ := hs
    obtain ⟨ha,hb⟩ := hi (a,b) (by simp)
    exact ⟨hacc,ha,hb,hprod,ih _ htail (fun p hp => hi p (by simp [hp]))⟩

/-- All partial sums and pair products are bounded by a quadratic function
of the two actual serialized streams and initial accumulator. -/
theorem dotBitBound_stream (acc : ℤ) (ps : List (ℤ×ℤ)) :
    DotBitBound (2*(dotStreamLength acc ps)^2+2*dotStreamLength acc ps+2) acc ps := by
  let N := dotStreamLength acc ps
  have haccLen : (signedBits acc).length≤N := by dsimp [N,dotStreamLength]; omega
  have hacc := abs_le_pow_signed_length acc N haccLen
  have hpair (p : ℤ×ℤ) (hp : p∈ps) : (p.1*p.2).natAbs≤2^(2*N) := by
    obtain ⟨ha,hb⟩ := dot_pair_length acc ps p hp
    have hm := Nat.mul_le_mul (abs_le_pow_signed_length p.1 N ha) (abs_le_pow_signed_length p.2 N hb)
    simpa [Int.natAbs_mul,←pow_add,show N+N=2*N by omega] using hm
  have hs := sumBitBound_of_abs N (2*N) acc (ps.map (fun p => p.1*p.2)) hacc (by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    exact hpair p hp)
  have hlen := dot_list_length acc ps
  have hmul := Nat.mul_le_mul_left (2*N+1) hlen
  have hs' : SumBitBound (2*N^2+2*N+2) acc (ps.map (fun p => p.1*p.2)) := by
    apply hs.mono
    simp only [List.length_map]
    dsimp [N] at *
    nlinarith
  apply dotBitBound_of_sum acc ps hs'
  intro p hp
  obtain ⟨ha,hb⟩ := dot_pair_length acc ps p hp
  dsimp [N] at *
  constructor <;> nlinarith

noncomputable def dotAccumulatorTime : Polynomial ℕ :=
  1+Polynomial.X*(50*(2*(2*Polynomial.X^2+2*Polynomial.X+2)+1)^3+
    400*(2*Polynomial.X^2+2*Polynomial.X+3)+11*(2*Polynomial.X^2+2*Polynomial.X+2)+30)

/-- No intermediate-size or runtime certificate remains in this theorem: the
actual finite program and its degree-seven polynomial are fully constructed. -/
theorem dotAccumulator_polynomial (g : BitString → ℕ) (ps : List (ℤ×ℤ)) (acc : ℤ) :
    ∃ t, dotAccumulator.Executes g
      (dotStore [] [] [] [] [] [] (signedBits acc)
        (encodeBitList (ps.map (fun p => signedBits p.1))) (encodeBitList (ps.map (fun p => signedBits p.2))))
      (dotStore [] [] [] [] [] [] (signedBits (acc+(ps.map (fun p => p.1*p.2)).sum)) [] []) t ∧
      t≤dotAccumulatorTime.eval (dotStreamLength acc ps) := by
  obtain ⟨t,ht,hbound⟩ := dotAccumulator_executes g ps acc _ (dotBitBound_stream acc ps)
  refine ⟨t,ht,hbound.trans ?_⟩
  simp only [dotAccumulatorTime,Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_ofNat,dotIterationBound]
  convert Nat.add_le_add_left (Nat.mul_le_mul_right
    (50*(2*(2*(dotStreamLength acc ps)^2+2*dotStreamLength acc ps+2)+1)^3+
      400*(2*(dotStreamLength acc ps)^2+2*dotStreamLength acc ps+3)+
      11*(2*(dotStreamLength acc ps)^2+2*dotStreamLength acc ps+2)+30)
    (dot_list_length acc ps)) 1 using 1 <;> congr 1 <;> ring

/-- Direct two-list interface for the weighted sums in interpolation. -/
theorem dotAccumulator_zip_polynomial (g : BitString → ℕ) (xs ys : List ℤ) (acc : ℤ)
    (hlen : xs.length=ys.length) :
    ∃ t, dotAccumulator.Executes g
      (dotStore [] [] [] [] [] [] (signedBits acc)
        (encodeBitList (xs.map signedBits)) (encodeBitList (ys.map signedBits)))
      (dotStore [] [] [] [] [] [] (signedBits (acc+(List.zipWith (·*·) xs ys).sum)) [] []) t ∧
      t≤dotAccumulatorTime.eval ((signedBits acc).length+
        (encodeBitList (xs.map signedBits)).length+(encodeBitList (ys.map signedBits)).length) := by
  have hx : (xs.zip ys).map (fun p => signedBits p.1)=xs.map signedBits := by
    change (xs.zip ys).map (signedBits ∘ Prod.fst)=xs.map signedBits
    rw [←List.map_map,List.map_fst_zip hlen.le]
  have hy : (xs.zip ys).map (fun p => signedBits p.2)=ys.map signedBits := by
    change (xs.zip ys).map (signedBits ∘ Prod.snd)=ys.map signedBits
    rw [←List.map_map,List.map_snd_zip hlen.ge]
  have hp : (xs.zip ys).map (fun p => p.1*p.2)=List.zipWith (·*·) xs ys := List.map_uncurry_zip_eq_zipWith
  simpa only [dotStreamLength,hx,hy,hp] using dotAccumulator_polynomial g (xs.zip ys) acc

end HiddenCircuits.Complexity.BinaryArithmetic
