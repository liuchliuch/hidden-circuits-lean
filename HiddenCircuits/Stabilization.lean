import HiddenCircuits.MatrixPotential

/-! Exact stabilization under a no-return idempotent filter and bounded flow.
Concrete filter matrices must discharge every structural hypothesis. -/
namespace HiddenCircuits
open scoped BigOperators

section Algebra
variable {R : Type*} [Ring R] (D N : R)

/-- Terms with a single contiguous run of the idempotent letter. -/
def oneBlock (m : ℕ) : R := ∑ a ∈ Finset.range (m+1), N^a * D * N^(m-a)

lemma oneBlock_zero : oneBlock D N 0 = D := by simp [oneBlock]

lemma left_D_oneBlock (hD : D*D=D)
    (hsep : ∀ a : ℕ, 0 < a → D*N^a*D=0) (m : ℕ) :
    D * oneBlock D N m = D * N^m := by
  unfold oneBlock
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single 0]
  · simp [← mul_assoc,hD]
  · intro a ha ha0
    have hz := hsep a (by omega)
    calc
      D * (N^a*D*N^(m-a)) = (D*N^a*D)*N^(m-a) := by noncomm_ring
      _ = 0 := by rw [hz,zero_mul]
  · simp

lemma oneBlock_succ (m : ℕ) :
    oneBlock D N (m+1) = D*N^(m+1) + N*oneBlock D N m := by
  unfold oneBlock
  rw [Finset.sum_range_succ']
  simp only [pow_zero,one_mul,Nat.sub_zero]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [Nat.add_sub_add_right,pow_succ']
  noncomm_ring

/-- The exact consecutive-power difference; no commutativity of D and N is used. -/
theorem power_difference (hD : D*D=D)
    (hsep : ∀ a : ℕ, 0 < a → D*N^a*D=0) (m : ℕ) :
    (D+N)^(m+1) - (D+N)^m = N^(m+1) - N^m + oneBlock D N m := by
  induction m with
  | zero => simp [oneBlock]; noncomm_ring
  | succ m ih =>
    have hdiff : (D+N)^((m+1)+1)-(D+N)^(m+1) =
        (D+N)*((D+N)^(m+1)-(D+N)^m) := by
      rw [mul_sub,← pow_succ',← pow_succ']
    rw [hdiff,ih,oneBlock_succ]
    have hb := left_D_oneBlock D N hD hsep m
    rw [pow_succ' N (m+1),pow_succ' N m]
    noncomm_ring [hb]

/-- If all flow terms beyond d vanish, consecutive powers are exactly equal. -/
theorem stable_power (hD : D*D=D)
    (hsep : ∀ a : ℕ, 0 < a → D*N^a*D=0)
    (d : ℕ) (hN : N^(d+1)=0)
    (hmix : ∀ a b : ℕ, d < a+b → N^a*D*N^b=0) :
    (D+N)^((d+1)+1) = (D+N)^(d+1) := by
  have h := power_difference D N hD hsep (d+1)
  have hb : oneBlock D N (d+1)=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have ha' : a ≤ d+1 := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    exact hmix a (d+1-a) (by omega)
  have hn : N^((d+1)+1)=0 := by rw [pow_succ,hN,zero_mul]
  rw [hn,hN,hb] at h
  simpa only [sub_zero,zero_add,sub_eq_zero] using h

lemma powers_eq_after {A : R} {m : ℕ} (h : A^(m+1)=A^m) :
    ∀ n, m ≤ n → A^n=A^m := by
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,pow_succ,ih (by omega)]
    simpa only [pow_succ] using h

/-- Once stable, the stabilized power is an actual idempotent. -/
theorem stable_power_idempotent {A : R} {m : ℕ} (h : A^(m+1)=A^m) :
    A^m*A^m=A^m := by
  rw [← pow_add]
  exact powers_eq_after h (m+m) (by omega)

end Algebra
section Matrix
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Mixed flow is bounded by the same potential width even with a preserving operator in between. -/
theorem potential_mixed_vanish (D N : Matrix ι ι R) (ω : ι → ℕ) (lo d : ℕ)
    (hN : ∀ i j, N i j ≠ 0 → ω i + 1 ≤ ω j)
    (hD : ∀ i j, D i j ≠ 0 → ω i ≤ ω j)
    (hlo : ∀ i, lo ≤ ω i) (hhi : ∀ i, ω i ≤ lo+d)
    (a b : ℕ) (hab : d < a+b) : N^a*D*N^b=0 := by
  ext i j
  by_contra h
  rw [Matrix.mul_apply] at h
  obtain ⟨z,_,hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hl : (N^a*D) i z ≠ 0 := fun he => hz (by rw [he,zero_mul])
  have hr : (N^b) z j ≠ 0 := fun he => hz (by rw [he,mul_zero])
  rw [Matrix.mul_apply] at hl
  obtain ⟨w,_,hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
  have hnw : (N^a) i w ≠ 0 := fun he => hw (by rw [he,zero_mul])
  have hdw : D w z ≠ 0 := fun he => hw (by rw [he,mul_zero])
  have h1 := potential_pow_support N ω hN a i w hnw
  have h2 := hD w z hdw
  have h3 := potential_pow_support N ω hN b z j hr
  have h4 := hlo i
  have h5 := hhi j
  omega

/-- Genuine generic stabilization from structural support, separation and idempotence. -/
theorem bounded_flow_stabilizes (D N : Matrix ι ι R) (ω : ι → ℕ) (lo d : ℕ)
    (hid : D*D=D) (hsep : ∀ a : ℕ, 0<a → D*N^a*D=0)
    (hN : ∀ i j, N i j ≠ 0 → ω i + 1 ≤ ω j)
    (hD : ∀ i j, D i j ≠ 0 → ω i ≤ ω j)
    (hlo : ∀ i, lo ≤ ω i) (hhi : ∀ i, ω i ≤ lo+d) :
    (∀ n, d+1 ≤ n → (D+N)^n=(D+N)^(d+1)) ∧
      (D+N)^(d+2)*(D+N)^(d+2)=(D+N)^(d+2) := by
  have hs := stable_power D N hid hsep d (potential_nilpotent N ω lo d hN hlo hhi)
    (potential_mixed_vanish D N ω lo d hN hD hlo hhi)
  have hall := powers_eq_after hs
  refine ⟨hall,?_⟩
  apply stable_power_idempotent
  rw [hall ((d+2)+1) (by omega),hall (d+2) (by omega)]

end Matrix
end HiddenCircuits
