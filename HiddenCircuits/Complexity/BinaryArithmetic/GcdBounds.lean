import HiddenCircuits.Complexity.BinaryArithmetic.Division

/-! A bit-length bound for Euclid's actual remainder iteration. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.Gcd

def steps (m n : ℕ) : ℕ :=
  if h : n=0 then 0 else 1+steps n (m%n)
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem steps_zero (m : ℕ) : steps m 0=0 := by rw [steps];simp
lemma steps_succ (m n : ℕ) (hn : n≠0) : steps m n=1+steps n (m%n) := by
  rw [steps];simp [hn]

/-- Two consecutive nonterminal remainders at least halve the old divisor. -/
lemma twice_mod_lt (n r : ℕ) (hr : 0<r) (hlt : r<n) : 2*(n%r)<n := by
  have hm:=Nat.mod_lt n hr
  by_cases hh : 2*r≤n
  · omega
  · have hn : n<r+r := by omega
    rw [Nat.mod_eq_sub_mod hlt.le, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The number of actual long divisions is at most twice the divisor's bit length. -/
theorem steps_lt_pow (k m n : ℕ) (hn : n<2^k) : steps m n≤2*k := by
  induction k generalizing m n with
  | zero =>
    have he:n=0 := by simpa using hn
    subst n;simp
  | succ k ih =>
    by_cases hz : n=0
    · subst n;simp
    · rw [steps_succ m n hz]
      by_cases hr : m%n=0
      · rw [hr,steps_zero];omega
      · rw [steps_succ n (m%n) hr]
        have hrem:=twice_mod_lt n (m%n) (Nat.pos_of_ne_zero hr) (Nat.mod_lt m (Nat.pos_of_ne_zero hz))
        have hb : n%(m%n)<2^k := by rw [pow_succ] at hn;omega
        have hi:=ih (m%n) (n%(m%n)) hb
        omega

theorem steps_length (m n : ℕ) : steps m n≤2*(Computability.encodeNat n).length := by
  apply steps_lt_pow
  simpa using value_lt_pow_length (Computability.encodeNat n)

lemma bits_length_mono (m n : ℕ) (h : m≤n) :
    (Computability.encodeNat m).length≤(Computability.encodeNat n).length :=
  canonical_length_mono (canonical_encodeNat _) (canonical_encodeNat _) (by simpa)

end HiddenCircuits.Complexity.BinaryArithmetic.Gcd
