import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Size
import HiddenCircuits.EntryBounds
import HiddenCircuits.IntegralTransfers
import Mathlib.Tactic

/-! Explicit polynomial exponents for the paper's normalized-transfer integer envelopes. -/
namespace HiddenCircuits

lemma succ_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; nlinarith [Nat.one_le_pow n 2 (by decide)]

lemma factorial_le_two_pow_square (p : ℕ) : p.factorial ≤ 2^(p^2) := by
  calc
    p.factorial ≤ p^p := Nat.factorial_le_pow p
    _ ≤ (2^p)^p := Nat.pow_le_pow_left (by have := succ_le_two_pow p; omega) p
    _ = _ := by rw [← pow_mul]; congr 1; ring

def transferDimension (p : ℕ) := (2*p).choose p
def inverseEnvelope (p : ℕ) := (p^2+1)*((transferDimension p+1)*p.factorial)^(p^2)
def normalizedEnvelope (p : ℕ) := transferDimension p*p.factorial*inverseEnvelope p
def transferBitPolynomial (p g : ℕ) := (p^4+2*p^3+3*p^2+4*p+2)*g

lemma transferDimension_bound (p : ℕ) : transferDimension p ≤ 2^(2*p) :=
  Nat.choose_le_two_pow _ _

lemma transferDimension_succ_bound (p : ℕ) : transferDimension p+1 ≤ 2^(2*p+1) := by
  have h := transferDimension_bound p
  have h1 : 1 ≤ 2^(2*p) := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ]
  omega

lemma inverseEnvelope_bound (p : ℕ) :
    inverseEnvelope p ≤ 2^(p^2+1+(2*p+1+p^2)*p^2) := by
  have hb : (transferDimension p+1)*p.factorial ≤ 2^(2*p+1+p^2) := by
    rw [pow_add]
    exact Nat.mul_le_mul (transferDimension_succ_bound p) (factorial_le_two_pow_square p)
  have hm : p^2+1 ≤ 2^(p^2+1) := by
    have h := succ_le_two_pow (p^2+1)
    omega
  unfold inverseEnvelope
  calc
    _ ≤ 2^(p^2+1) * (2^(2*p+1+p^2))^(p^2) :=
      Nat.mul_le_mul hm (Nat.pow_le_pow_left hb (p^2))
    _ = _ := by rw [← pow_mul,← pow_add]

lemma normalizedEnvelope_bound (p : ℕ) :
    normalizedEnvelope p ≤ 2^(2*p+p^2+(p^2+1+(2*p+1+p^2)*p^2)) := by
  unfold normalizedEnvelope
  rw [pow_add,pow_add]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (transferDimension_bound p) (factorial_le_two_pow_square p))
    (inverseEnvelope_bound p)

/-- Explicit envelope for g operations on the half-filled N=2p subset space. -/
theorem transfer_word_envelope (p g : ℕ) :
    ((transferDimension p+1)*max 1 (normalizedEnvelope p))^g ≤ 2^(transferBitPolynomial p g) := by
  have hm : max 1 (normalizedEnvelope p) ≤
      2^(2*p+p^2+(p^2+1+(2*p+1+p^2)*p^2)) :=
    max_le (Nat.one_le_pow _ _ (by decide)) (normalizedEnvelope_bound p)
  have hbase := Nat.mul_le_mul (transferDimension_succ_bound p) hm
  rw [← pow_add] at hbase
  have hh := Nat.pow_le_pow_left hbase g
  rw [← pow_mul] at hh
  convert hh using 1 <;> unfold transferBitPolynomial <;> congr 1 <;> ring

lemma letterMagnitude_eq_normalizedEnvelope (p : ℕ) : letterMagnitude p = normalizedEnvelope p := by
  have hp : 2*p-p=p := by omega
  simp [letterMagnitude,normalizedEnvelope,inverseMagnitude,inverseEnvelope,transferDimension,hp,pow_two]

/-- Exponential envelope on an entry of the actual permanent-defined word matrix. -/
theorem word_entry_polynomial_envelope (p : ℕ) (w : List (Letter (2*p)))
    (S T : State (2*p) p) :
    |wordMatrix p w S T| ≤ (2^(transferBitPolynomial p w.length) : ℕ) := by
  have h := word_entry_bound p w S T
  rw [letterMagnitude_eq_normalizedEnvelope] at h
  apply h.trans
  exact_mod_cast transfer_word_envelope p w.length

/-- Lemma3.2's integer output has polynomially many magnitude bits plus one sign bit. -/
theorem WordInstance.value_integer_bit_bound (w : WordInstance) :
    ∃ z : ℤ, w.value = (z : ℚ) ∧
      z.natAbs ≤ 2^(transferBitPolynomial w.particles w.word.length) ∧
      z.natAbs.size + 1 ≤ transferBitPolynomial w.particles w.word.length + 2 := by
  obtain ⟨z,hz⟩ := w.value_integral
  have hb := word_entry_polynomial_envelope w.particles w.word w.source w.target
  change |w.value| ≤ _ at hb
  rw [hz,← Int.cast_abs,← Nat.cast_natAbs] at hb
  have hn : z.natAbs ≤ 2^(transferBitPolynomial w.particles w.word.length) := by exact_mod_cast hb
  refine ⟨z,hz,hn,?_⟩
  have hs := Nat.size_le_size hn
  rw [Nat.size_pow] at hs
  omega

/-- One-variable polynomial bound in the paper's number of tracks plus word length. -/
theorem transferBitPolynomial_input_bound (p g : ℕ) :
    transferBitPolynomial p g + 2 ≤ 14*(2*p+g+1)^5 := by
  let s := 2*p+g+1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hp : p ≤ s := by dsimp [s]; omega
  have hg : g ≤ s := by dsimp [s]; omega
  have hpow (k : ℕ) (hk : k ≤ 4) : p^k ≤ s^4 :=
    (Nat.pow_le_pow_left hp k).trans (Nat.pow_le_pow_right hs hk)
  have h0 := hpow 0 (by decide)
  have h1 := hpow 1 (by decide)
  have h2 := hpow 2 (by decide)
  have h3 := hpow 3 (by decide)
  have h4 := hpow 4 (by decide)
  have hb : p^4+2*p^3+3*p^2+4*p+2 ≤ 12*s^4 := by
    simp only [pow_zero,pow_one] at h0 h1
    omega
  have hmul := Nat.mul_le_mul hb hg
  have h5 : 1 ≤ s^5 := Nat.one_le_pow _ _ hs
  change transferBitPolynomial p g+2 ≤ 14*s^5
  unfold transferBitPolynomial
  nlinarith [show s^4*s=s^5 by ring]

/-- Actual WordEval output with an explicit bit bound polynomial in N+word length. -/
theorem WordInstance.value_bit_bound_tracks (w : WordInstance) :
    ∃ z : ℤ, w.value = (z : ℚ) ∧
      z.natAbs.size+1 ≤ 14*(2*w.particles+w.word.length+1)^5 := by
  obtain ⟨z,hz,_,hb⟩ := w.value_integer_bit_bound
  exact ⟨z,hz,hb.trans (transferBitPolynomial_input_bound _ _)⟩

end HiddenCircuits
