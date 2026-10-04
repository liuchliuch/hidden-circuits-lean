import HiddenCircuits.Approximation.FiniteChains.CoinTools
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Unbounded rejection from independent finite fair-coin blocks

This is a separate, expected-time model, not `RandomBitProgram`: arbitrarily
many blocks may be consumed. A terminating run is a finite sequence of rejected
blocks followed by one accepted block. Its probability is the fair-bit cylinder
weight. The sum of these disjoint cylinder weights is proved to be one.
-/
namespace HiddenCircuits.ExactSampling.Rejection
open HiddenCircuits.Approximation HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators

/-- Minimum width covering `[0,n)`. In particular the singleton draws no bits. -/
def width (n : ℕ) : ℕ := Nat.size (n-1)
def capacity (n : ℕ) : ℕ := 2^width n

theorem capacity_pos (n : ℕ) : 0<capacity n := by unfold capacity; positivity

theorem covered {n : ℕ} (hn : 0<n) : n≤capacity n := by
  have h := Nat.lt_size_self (n-1)
  unfold capacity width
  omega

theorem capacity_lt_twice {n : ℕ} (hn : 0<n) : capacity n<2*n := by
  by_cases h : width n=0
  · simp [capacity,h]; omega
  · have hw : width n-1<width n := by omega
    have hh := Nat.lt_size.mp hw
    change 2^(width n-1)≤n-1 at hh
    have he : width n=(width n-1)+1 := by omega
    rw [capacity,he,pow_succ]
    omega

theorem width_le_size (n : ℕ) : width n≤Nat.size n := Nat.size_le_size (by omega)

/-- One bounded-integer proposal. Rejection has its own visible result. -/
def attempt (n : ℕ) (r : CoinTape (width n)) : Option (Fin n) :=
  if h : (tapeNumber (width n) r).val<n then some ⟨_,h⟩ else none

def acceptedTape {n : ℕ} (hn : 0<n) (i : Fin n) : CoinTape (width n) :=
  (tapeNumber (width n)).symm ⟨i.val,i.isLt.trans_le (covered hn)⟩

@[simp] theorem attempt_accepted {n : ℕ} (hn : 0<n) (i : Fin n) :
    attempt n (acceptedTape hn i)=some i := by
  simp [attempt,acceptedTape,i.isLt]

 theorem attempt_eq_some_iff {n : ℕ} (hn : 0<n) (r : CoinTape (width n)) (i : Fin n) :
    attempt n r=some i ↔ r=acceptedTape hn i := by
  constructor
  · intro h
    unfold attempt at h
    split_ifs at h with hi
    · have he : (tapeNumber (width n) r).val=i.val := congrArg Fin.val (Option.some.inj h)
      apply (tapeNumber (width n)).injective
      simp only [acceptedTape,Equiv.apply_symm_apply]
      exact Fin.ext he
  · rintro rfl; exact attempt_accepted hn i

 theorem attempt_probability {n : ℕ} (hn : 0<n) (i : Fin n) :
    coinProbability (width n) (fun r => attempt n r=some i)=1/(capacity n : ℚ) := by
  rw [coinProbability_congr (fun r => attempt_eq_some_iff hn r i),coinProbability_singleton]
  simp [capacity]

/-- Rejected blocks are actual fair-bit words, not ideal random integers. -/
def Rejected (n : ℕ) := {r : CoinTape (width n) // attempt n r=none}

noncomputable instance (n : ℕ) : Fintype (Rejected n) := by
  classical
  unfold Rejected
  infer_instance

/-- Each rejected word has a unique integer offset from the cutoff. -/
def rejectedEquiv (n : ℕ) : Rejected n ≃ Fin (capacity n-n) where
  toFun r := ⟨(tapeNumber (width n) r.val).val-n,by
    have hlt := (tapeNumber (width n) r.val).isLt
    have hn : n≤(tapeNumber (width n) r.val).val := by
      by_contra h
      have hr := r.property
      simp [attempt,Nat.lt_of_not_ge h] at hr
    change _<2^width n-n
    omega⟩
  invFun j := ⟨(tapeNumber (width n)).symm ⟨j.val+n,by
    have hj := j.isLt
    change j.val+n<2^width n
    change j.val<2^width n-n at hj
    omega⟩,by simp [attempt]⟩
  left_inv r := by
    apply Subtype.ext
    apply (tapeNumber (width n)).injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    have hn : n≤(tapeNumber (width n) r.val).val := by
      by_contra h
      have hr := r.property
      simp [attempt,Nat.lt_of_not_ge h] at hr
    exact Nat.sub_add_cancel hn
  right_inv j := by
    apply Fin.ext
    simp

@[simp] theorem card_rejected (n : ℕ) : Fintype.card (Rejected n)=capacity n-n :=
  (Fintype.card_congr (rejectedEquiv n)).trans (Fintype.card_fin _)

/-- An outcome-indexed terminating trace: `t` rejected blocks followed by the
unique accepted block for `i`. No bounded retry limit occurs in this type. -/
def Trace (n t : ℕ) := Fin t → Rejected n

noncomputable instance (n t : ℕ) : Fintype (Trace n t) := by unfold Trace; infer_instance

def traceWord {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) : List Bool :=
  (List.ofFn (fun j => List.ofFn (r j).val)).flatten ++ List.ofFn (acceptedTape hn i)

 theorem traceWord_length {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) :
    (traceWord hn t r i).length=(t+1)*width n := by
  simp [traceWord,List.length_flatten,List.sum_ofFn]
  ring

/-- Sum of the individual fair-bit cylinder weights for one outcome and retry
count. The cardinality is derived from actual rejected words. -/
noncomputable def outcomeMass (n t : ℕ) : ℝ :=
  (Fintype.card (Trace n t) : ℝ)/(2^((t+1)*width n) : ℝ)

noncomputable def rejectRatio (n : ℕ) : ℝ := (capacity n-n : ℕ)/(capacity n : ℝ)

 theorem outcomeMass_eq (n t : ℕ) :
    outcomeMass n t=rejectRatio n^t/(capacity n : ℝ) := by
  simp only [outcomeMass,Trace,Fintype.card_fun,Fintype.card_fin,card_rejected,
    Nat.cast_pow,rejectRatio,div_pow]
  rw [add_mul,one_mul,pow_add,pow_mul]
  simp only [capacity,Nat.cast_pow,Nat.cast_ofNat]
  ring

 theorem rejectRatio_nonneg (n : ℕ) : 0≤rejectRatio n := by unfold rejectRatio; positivity

 theorem one_sub_rejectRatio {n : ℕ} (hn : 0<n) :
    1-rejectRatio n=(n : ℝ)/capacity n := by
  have hQ : (capacity n : ℝ)≠0 := by exact_mod_cast (capacity_pos n).ne'
  rw [rejectRatio,Nat.cast_sub (covered hn)]
  field_simp
  ring

 theorem rejectRatio_lt_half {n : ℕ} (hn : 0<n) : rejectRatio n<1/2 := by
  have hQ : (0:ℝ)<capacity n := by exact_mod_cast capacity_pos n
  have hc : (capacity n : ℝ)<2*n := by exact_mod_cast capacity_lt_twice hn
  rw [rejectRatio,Nat.cast_sub (covered hn)]
  apply (div_lt_iff₀ hQ).mpr
  linarith

 theorem rejectRatio_lt_one {n : ℕ} (hn : 0<n) : rejectRatio n<1 :=
  (rejectRatio_lt_half hn).trans (by norm_num)

/-- Exact output law, with no conditioning on eventual success. -/
 theorem outcomeMass_hasSum {n : ℕ} (hn : 0<n) :
    HasSum (outcomeMass n) (1/(n : ℝ)) := by
  have hh := (hasSum_geometric_of_lt_one (rejectRatio_nonneg n) (rejectRatio_lt_one hn)).div_const
    (capacity n : ℝ)
  simp only [←outcomeMass_eq] at hh
  convert hh using 1
  rw [one_sub_rejectRatio hn]
  have hQ : (capacity n : ℝ)≠0 := by exact_mod_cast (capacity_pos n).ne'
  have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

 theorem outcomeMass_sum {n : ℕ} (hn : 0<n) :
    ∑' t, outcomeMass n t=1/(n : ℝ) := (outcomeMass_hasSum hn).tsum_eq

/-- Total mass of all finite terminating traces is one. Thus the operational
rejection loop terminates almost surely, including non-power-of-two ranges. -/
 theorem terminates_almost_surely {n : ℕ} (hn : 0<n) :
    ∑' t, (n : ℝ)*outcomeMass n t=1 := by
  have hh := (outcomeMass_hasSum hn).mul_left (n : ℝ)
  have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  simpa [hn'] using hh.tsum_eq

/-- The probability that another trial is needed after `t` rejections. -/
noncomputable def tailMass (n t : ℕ) : ℝ := rejectRatio n^t

 theorem tailMass_tendsto_zero {n : ℕ} (hn : 0<n) :
    Filter.Tendsto (tailMass n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (rejectRatio_nonneg n) (rejectRatio_lt_one hn)

/-- Tail-sum definition of the number of trials actually executed. -/
noncomputable def expectedAttempts (n : ℕ) : ℝ := ∑' t,tailMass n t

 theorem expectedAttempts_eq {n : ℕ} (hn : 0<n) :
    expectedAttempts n=(capacity n : ℝ)/n := by
  unfold expectedAttempts tailMass
  rw [tsum_geometric_of_lt_one (rejectRatio_nonneg n) (rejectRatio_lt_one hn),
    one_sub_rejectRatio hn,inv_div]

 theorem expectedAttempts_lt_two {n : ℕ} (hn : 0<n) : expectedAttempts n<2 := by
  rw [expectedAttempts_eq hn]
  apply (div_lt_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr
  exact_mod_cast capacity_lt_twice hn

/-- Every trial consumes exactly the binary width; no exponential unary integer
is constructed by the random driver. -/
noncomputable def expectedBits (n : ℕ) : ℝ := (width n : ℝ)*expectedAttempts n

 theorem expectedBits_le {n : ℕ} (hn : 0<n) : expectedBits n≤2*Nat.size n := by
  unfold expectedBits
  calc
    _ ≤ (width n : ℝ)*2 := mul_le_mul_of_nonneg_left (expectedAttempts_lt_two hn).le (by positivity)
    _ ≤ (Nat.size n : ℝ)*2 := by gcongr; exact_mod_cast width_le_size n
    _ = _ := by ring

@[simp] theorem width_one : width 1=0 := by simp [width]
@[simp] theorem attempt_zero (r : CoinTape (width 0)) : attempt 0 r=none := by simp [attempt]
@[simp] theorem attempt_one (r : CoinTape (width 1)) : attempt 1 r=some 0 := by
  have he : r=acceptedTape (by decide : 0<1) 0 := by
    funext i
    have hi := i.isLt
    simp at hi
  rw [he,attempt_accepted]

end HiddenCircuits.ExactSampling.Rejection
