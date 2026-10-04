import HiddenCircuits.ExactSampling.Rejection
import HiddenCircuits.Complexity.BinaryArithmetic.SubtractionMachine

/-!
# Operational rejection and charged binary proposals

The random driver consumes fresh blocks of fair bits until its actual binary
comparison accepts. A finite run records every rejected block and the final
accepted block. Deterministic comparison is the fixed four-stack subtraction
machine; even noncanonical random words are compared without unary expansion.
-/
namespace HiddenCircuits.ExactSampling.Rejection
open HiddenCircuits.Approximation HiddenCircuits.Approximation.FiniteChains
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic
open scoped BigOperators

/-- Exact first-hit semantics: there is no unconsumed random block in a run. -/
inductive Run (n : ℕ) : List (CoinTape (width n)) → Fin n → Prop
  | accept {r i} (accepted : attempt n r=some i) : Run n [r] i
  | reject {r rs i} (rejected : attempt n r=none) (tail : Run n rs i) : Run n (r::rs) i

def traceBlocks {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) :
    List (CoinTape (width n)) := List.ofFn (fun j => (r j).val) ++ [acceptedTape hn i]

 theorem traceBlocks_run {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) :
    Run n (traceBlocks hn t r i) i := by
  induction t with
  | zero => simpa [traceBlocks] using Run.accept (attempt_accepted hn i)
  | succ t ih =>
    simpa [traceBlocks,List.ofFn_succ] using
      Run.reject (r 0).property (ih (fun j => r j.succ))

@[simp] theorem traceBlocks_length {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) :
    (traceBlocks hn t r i).length=t+1 := by simp [traceBlocks]

/-- Every terminating operational run is one of the traces counted by the law. -/
 theorem Run.trace {n : ℕ} (hn : 0<n) {rs : List (CoinTape (width n))} {i : Fin n}
    (h : Run n rs i) : ∃t,∃r : Trace n t,rs=traceBlocks hn t r i := by
  induction h with
  | accept ha =>
    refine ⟨0,Fin.elim0,?_⟩
    simp only [traceBlocks,List.ofFn_zero,List.nil_append]
    exact congrArg (fun r => [r]) ((attempt_eq_some_iff hn _ _).mp ha)
  | @reject r rs i hr ht ih =>
    obtain ⟨t,s,rfl⟩ := ih
    refine ⟨t+1,Fin.cons ⟨r,hr⟩ s,?_⟩
    simp [traceBlocks,List.ofFn_succ]

/-- Two complete runs cannot have one as a proper prefix of the other. This is
what makes their fair-bit cylinder probabilities disjoint. -/
 theorem Run.prefix_free {n : ℕ} {xs ys : List (CoinTape (width n))} {i j : Fin n}
    (hx : Run n xs i) (hy : Run n ys j) (hp : xs.IsPrefix ys) : xs=ys ∧ i=j := by
  induction hx generalizing ys j with
  | @accept r i hr =>
    cases hy with
    | @accept s j hs =>
      have h : r=s := by simpa using hp
      subst s
      exact ⟨rfl,Option.some.inj (hr.symm.trans hs)⟩
    | @reject s rs j hs ht =>
      have h : r=s := by simpa using hp
      subst s
      rw [hr] at hs
      contradiction
  | @reject r rs i hr ht ih =>
    cases hy with
    | @accept s j hs =>
      have h : r=s := (List.cons_prefix_cons.mp hp).1
      subst s
      rw [hr] at hs
      contradiction
    | @reject s ss j hs hu =>
      obtain ⟨h,hpt⟩ := List.cons_prefix_cons.mp hp
      subst s
      obtain ⟨rfl,rfl⟩ := ih hu hpt
      exact ⟨rfl,rfl⟩

 theorem traceBlocks_injective {n : ℕ} (hn : 0<n) (t : ℕ) (i : Fin n) :
    Function.Injective (fun r : Trace n t => traceBlocks hn t r i) := by
  intro r s h
  have h' : List.ofFn (fun j => (r j).val)=List.ofFn (fun j => (s j).val) :=
    List.append_cancel_right h
  have he := List.ofFn_injective h'
  funext j
  exact Subtype.ext (congrFun he j)

 theorem traceWord_eq_flatten {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) :
    traceWord hn t r i=((traceBlocks hn t r i).map List.ofFn).flatten := by
  simp [traceWord,traceBlocks,List.map_ofFn,Function.comp_def]

/-- Actual little-endian decoder agrees with the bijection used in fair-coin
counting. This holds for words with redundant high zeros as well. -/
 theorem value_ofFn (m : ℕ) (r : CoinTape m) : value (List.ofFn r)=(tapeNumber m r).val := by
  have hs : value (List.ofFn r)=∑i : Fin m,bitVal (r i)*2^i.val := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.ofFn_succ,value_cons,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
      simp_rw [←Nat.mul_assoc]
      rw [←Finset.sum_mul]
      ring
  rw [hs]
  unfold tapeNumber
  rw [Equiv.trans_apply,finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change bitVal (r i)=(finTwoEquiv.symm (r i)).val
  cases r i <;> rfl

/-- The flag produced by the actual binary subtraction code is precisely the
proposal's acceptance predicate. -/
 theorem proposal_compare_executes (n : ℕ) (r : CoinTape (width n)) (g : BitString→ℕ) :
    subBlock.Executes g (subStore (List.ofFn r) (Computability.encodeNat n) [] [])
      (subStore (subtractBits (List.ofFn r) (Computability.encodeNat n)) [] []
        [decide ((attempt n r).isSome)])
      (subCost (List.ofFn r) (Computability.encodeNat n)) := by
  have h := subBlock_executes g (List.ofFn r) (Computability.encodeNat n)
  have he : (subRaw (List.ofFn r) (Computability.encodeNat n) false).2=
      decide ((attempt n r).isSome) := by
    apply Bool.eq_iff_iff.mpr
    rw [subRaw_borrow,value_encodeNat,value_ofFn]
    by_cases ha : (tapeNumber (width n) r).val<n <;> simp [attempt,ha]
  rwa [he] at h

/-- Charge every random bit and every binary-comparison instruction. The bound
is linear in the binary size of `n`, not in its potentially exponential value. -/
def trialCost (n : ℕ) (r : CoinTape (width n)) : ℕ :=
  width n+subCost (List.ofFn r) (Computability.encodeNat n)

 theorem trialCost_bound (n : ℕ) (r : CoinTape (width n)) : trialCost n r≤6*Nat.size n+4 := by
  have hs := subCost_bound (List.ofFn r) (Computability.encodeNat n)
  simp only [List.length_ofFn,encodeNat_length] at hs
  rw [max_eq_right (width_le_size n)] at hs
  have hw := width_le_size n
  unfold trialCost
  omega

/-- Bit cost of all actual proposal comparisons in a completed trace. -/
def traceCost {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) : ℕ :=
  ((traceBlocks hn t r i).map (trialCost n)).sum

 theorem traceCost_bound {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) :
    traceCost hn t r i≤(t+1)*(6*Nat.size n+4) := by
  have h : ∀xs : List (CoinTape (width n)),
      (xs.map (trialCost n)).sum≤xs.length*(6*Nat.size n+4) := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hc := trialCost_bound n x
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  simpa [traceCost] using h (traceBlocks hn t r i)

/-- The expected number of trials computed from terminal traces agrees with
the tail-sum expectation. It is not merely a chosen cost annotation. -/
 theorem weighted_attempts_hasSum {n : ℕ} (hn : 0<n) :
    HasSum (fun t => ((t+1 : ℕ) : ℝ)*(n : ℝ)*outcomeMass n t) (expectedAttempts n) := by
  have hnorm : ‖rejectRatio n‖<1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (rejectRatio_nonneg n)]
    exact rejectRatio_lt_one hn
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one (rejectRatio_nonneg n) (rejectRatio_lt_one hn))
  have hh := (h.mul_right (n : ℝ)).div_const (capacity n : ℝ)
  convert hh using 1
  · funext t
    rw [outcomeMass_eq]
    push_cast
    ring
  · rw [expectedAttempts_eq hn,one_sub_rejectRatio hn]
    have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    have hQ : (capacity n : ℝ)≠0 := by exact_mod_cast (capacity_pos n).ne'
    have hr := one_sub_rejectRatio hn
    field_simp at hr ⊢
    nlinarith

/-- A uniform bound on the expectation of all random reads and comparison
instructions, derived from the distribution of complete operational traces. -/
 theorem expected_trial_work_le {n : ℕ} (hn : 0<n) :
    ∑' t, ((t+1 : ℕ) : ℝ)*(6*Nat.size n+4)*(n : ℝ)*outcomeMass n t≤
      2*(6*Nat.size n+4) := by
  have hh := (weighted_attempts_hasSum hn).mul_left (6*(Nat.size n : ℝ)+4)
  have he : (∑' t, ((t+1 : ℕ) : ℝ)*(6*Nat.size n+4)*(n : ℝ)*outcomeMass n t)=
      (6*(Nat.size n : ℝ)+4)*expectedAttempts n := by
    convert hh.tsum_eq using 1
    congr 1
    funext t
    ring
  rw [he]
  nlinarith [expectedAttempts_lt_two hn]

end HiddenCircuits.ExactSampling.Rejection
