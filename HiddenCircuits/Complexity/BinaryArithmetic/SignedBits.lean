import HiddenCircuits.Complexity.BinaryArithmetic.Multiplication

/-! Canonical signed magnitude, including a unique positive zero. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

def negative (z : ℤ) : Bool := decide (z<0)
def signedBits (z : ℤ) : BitString := negative z::Computability.encodeNat z.natAbs

def signedNat (b : Bool) (n : ℕ) : ℤ := if b then -(n : ℤ) else (n : ℤ)

@[simp] theorem signedNat_self (z : ℤ) : signedNat (negative z) z.natAbs = z := by
  by_cases h : z<0
  · simp only [signedNat,negative,h,decide_true,ite_true]
    exact (Int.eq_neg_natAbs_of_nonpos h.le).symm
  · simp only [signedNat,negative,h,decide_false,Bool.false_eq_true,ite_false]
    exact Int.natAbs_of_nonneg (le_of_not_gt h)

theorem signedNat_mul (a b : Bool) (m n : ℕ) :
    signedNat (xor a b) (m*n) = signedNat a m*signedNat b n := by
  cases a <;> cases b <;> simp [signedNat]

def finishSigned (sign : Bool) (magnitude : BitString) : BitString :=
  if magnitude = [] then [false] else sign::magnitude

theorem encodeNat_eq_nil_iff (n : ℕ) : Computability.encodeNat n = [] ↔ n=0 := by
  constructor
  · intro h; have hv := value_encodeNat n; rw [h] at hv; exact hv.symm
  · rintro rfl; rfl

/-- A requested negative sign is suppressed for zero. -/
theorem finishSigned_encode (s : Bool) (n : ℕ) :
    finishSigned s (Computability.encodeNat n) = signedBits (signedNat s n) := by
  cases s <;> by_cases hn : n=0 <;>
    simp [finishSigned,signedBits,signedNat,negative,encodeNat_eq_nil_iff,hn] <;> omega

theorem finishSigned_mul (a b : ℤ) :
    finishSigned (xor (negative a) (negative b)) (Computability.encodeNat (a.natAbs*b.natAbs)) =
      signedBits (a*b) := by
  rw [finishSigned_encode,signedNat_mul,signedNat_self,signedNat_self]

/-- Signed exact division agrees with integer division, including negative
numerators and denominators. No rounding convention is being assumed. -/
theorem finishSigned_exact_div (a b : ℤ) (hb : b≠0) (hdiv : b ∣ a) :
    finishSigned (xor (negative a) (negative b)) (Computability.encodeNat (a.natAbs/b.natAbs)) =
      signedBits (a/b) := by
  rw [finishSigned_encode]
  congr 1
  apply (mul_left_inj' hb).mp
  rw [Int.ediv_mul_cancel hdiv]
  conv_rhs => rw [← signedNat_self a]
  conv_lhs => rhs; rw [← signedNat_self b]
  rw [← signedNat_mul,Nat.div_mul_cancel (Int.natAbs_dvd_natAbs.mpr hdiv)]
  have hx : xor (xor (negative a) (negative b)) (negative b) = negative a := by
    cases negative a <;> cases negative b <;> rfl
  rw [hx]

/-- Three ordinary bit instructions suffice to attach the canonical sign. -/
abbrev finishOn {k : ℕ} (stack : Fin (k+1)) (sign : Bool) : OracleBlock k where
  labelCount := 6
  start := 0
  exit := 5
  code q := if q = 0 then .pop stack 3 1 2
    else if q = 1 then .push stack false 4
    else if q = 2 then .push stack true 4
    else if q = 3 then .push stack false 5
    else if q = 4 then .push stack sign 5
    else .halt
  exit_halt := rfl

def finishCost (magnitude : BitString) : ℕ := if magnitude=[] then 2 else 3

lemma finishCost_le (magnitude : BitString) : finishCost magnitude ≤ 3 := by
  unfold finishCost; split <;> omega

theorem finishOn_executes {k : ℕ} (g : BitString → ℕ) (stack : Fin (k+1)) (sign : Bool) (s : Store k) :
    (finishOn stack sign).Executes g s (Function.update s stack (finishSigned sign (s stack))) (finishCost (s stack)) := by
  cases hs : s stack with
  | nil =>
    have hp : (finishOn stack sign).machine.step g ((finishOn stack sign).config 0 s) =
        some ((finishOn stack sign).config 3 s,1) := by
      simp [OracleMachine.step,machine,config,finishOn,hs]
    have hq : (finishOn stack sign).machine.step g ((finishOn stack sign).config 3 s) =
        some ((finishOn stack sign).config 5 (Function.update s stack [false]),1) := by
      simp [OracleMachine.step,machine,config,finishOn,hs]
    simpa [hs,finishSigned,finishCost] using (Steps.single hp).trans (Steps.single hq)
  | cons b bs =>
    have hp : (finishOn stack sign).machine.step g ((finishOn stack sign).config 0 s) =
        some ((finishOn stack sign).config (if b then 2 else 1) (Function.update s stack bs),1) := by
      cases b <;> simp [OracleMachine.step,machine,config,finishOn,hs]
    have hq : (finishOn stack sign).machine.step g
        ((finishOn stack sign).config (if b then 2 else 1) (Function.update s stack bs)) =
        some ((finishOn stack sign).config 4 s,1) := by
      have he : Function.update s stack (b::bs)=s := by rw [←hs]; exact Function.update_eq_self _ _
      cases b <;> simp [OracleMachine.step,machine,config,finishOn,he]
    have hr : (finishOn stack sign).machine.step g ((finishOn stack sign).config 4 s) =
        some ((finishOn stack sign).config 5 (Function.update s stack (sign::b::bs)),1) := by
      simp [OracleMachine.step,machine,config,finishOn,hs]
    simpa [hs,finishSigned,finishCost] using (Steps.single hp).trans ((Steps.single hq).trans (Steps.single hr))

lemma finishOn_queryFree {k : ℕ} (stack : Fin (k+1)) (sign : Bool) : (finishOn stack sign).QueryFree := by
  intro q i o next; fin_cases q <;> simp [machine,finishOn]

variable {k : ℕ}

noncomputable def signedRight (B : OracleBlock (k+1)) (output : Fin (k+2)) (a : Bool) : OracleBlock (k+1) :=
  branchPop 1 skip (seq B (finishOn output (xor a false))) (seq B (finishOn output (xor a true)))

noncomputable def signedBinary (B : OracleBlock (k+1)) (output : Fin (k+2)) : OracleBlock (k+1) :=
  branchPop 0 skip (signedRight B output false) (signedRight B output true)

def withSigns (s : Store (k+1)) (a b : Bool) : Store (k+1) :=
  Function.update (Function.update s 0 (a::s 0)) 1 (b::s 1)

lemma signedRight_executes (B : OracleBlock (k+1)) (output : Fin (k+2)) (g : BitString → ℕ)
    {s t : Store (k+1)} {cost : ℕ} (h : B.Executes g s t cost) (a b : Bool) :
    (signedRight B output a).Executes g (Function.update s 1 (b::s 1))
      (Function.update t output (finishSigned (xor a b) (t output)))
      (cost+finishCost (t output)+4) := by
  have hup : Function.update (Function.update s (1 : Fin (k+2)) (b::s 1)) 1 (s 1)=s := by simp
  have hf := seq_executes B (finishOn output (xor a b)) g h
    (finishOn_executes g output (xor a b) t)
  cases b
  · have hb := branchPop_false (1 : Fin (k+2)) skip (seq B (finishOn output (xor a false)))
        (seq B (finishOn output (xor a true))) g
        (s := Function.update s 1 (false::s 1)) (rest := s 1) (by simp) (by rw [hup]; exact hf)
    convert hb using 1 <;> omega
  · have hb := branchPop_true (1 : Fin (k+2)) skip (seq B (finishOn output (xor a false)))
        (seq B (finishOn output (xor a true))) g
        (s := Function.update s 1 (true::s 1)) (rest := s 1) (by simp) (by rw [hup]; exact hf)
    convert hb using 1 <;> omega

/-- Finite sign dispatch adds two real pops, four continuation jumps, and at
most three sign-finishing instructions to a verified magnitude computation. -/
theorem signedBinary_executes (B : OracleBlock (k+1)) (output : Fin (k+2)) (g : BitString → ℕ)
    {s t : Store (k+1)} {cost : ℕ} (h : B.Executes g s t cost) (a b : Bool) :
    (signedBinary B output).Executes g (withSigns s a b)
      (Function.update t output (finishSigned (xor a b) (t output)))
      (cost+finishCost (t output)+6) := by
  have hup : Function.update (withSigns s a b) (0 : Fin (k+2)) (s 0) = Function.update s 1 (b::s 1) := by
    funext i
    by_cases h0 : i=0
    · subst i; simp [withSigns]
    · by_cases h1 : i=1
      · subst i; simp [withSigns]
      · simp [withSigns,Function.update_of_ne h0,Function.update_of_ne h1]
  have hs : withSigns s a b (0 : Fin (k+2)) = a::s 0 := by simp [withSigns]
  have hr := signedRight_executes B output g h a b
  cases a
  · have hb := branchPop_false (0 : Fin (k+2)) skip (signedRight B output false) (signedRight B output true) g
        hs (by rw [hup]; exact hr)
    convert hb using 1 <;> omega
  · have hb := branchPop_true (0 : Fin (k+2)) skip (signedRight B output false) (signedRight B output true) g
        hs (by rw [hup]; exact hr)
    convert hb using 1 <;> omega

lemma signedBinary_queryFree (B : OracleBlock (k+1)) (output : Fin (k+2)) (h : B.QueryFree) :
    (signedBinary B output).QueryFree := by
  have hr (a : Bool) : (signedRight B output a).QueryFree :=
    branchPop_queryFree _ _ _ _ skip_queryFree
      (seq_queryFree _ _ h (finishOn_queryFree _ _)) (seq_queryFree _ _ h (finishOn_queryFree _ _))
  exact branchPop_queryFree _ _ _ _ skip_queryFree (hr false) (hr true)

end HiddenCircuits.Complexity.BinaryArithmetic
