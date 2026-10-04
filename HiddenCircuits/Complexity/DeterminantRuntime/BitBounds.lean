import HiddenCircuits.Complexity.DeterminantRuntime.Faddeev
import HiddenCircuits.Complexity.DeterminantRuntime.Encoding

/-! Polynomial bit growth of every actual integer recurrence state.
The estimates follow from ordinary integer arithmetic, not supplied bounds. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open Matrix Finset BinaryArithmetic
variable {n : ℕ}

def EntriesBound (A : Matrix (Fin n) (Fin n) ℤ) (U : ℕ) : Prop :=
  ∀ i j, (A i j).natAbs ≤ U

theorem entriesBound_mul {A B : Matrix (Fin n) (Fin n) ℤ} {U V : ℕ}
    (hA : EntriesBound A U) (hB : EntriesBound B V) :
    EntriesBound (A * B) (n * (U * V)) := by
  intro i j
  calc
    _ ≤ ∑ k, (A i k * B k j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k : Fin n, U * V := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hA i k) (hB k j)
    _ = _ := by simp

theorem trace_abs_le {A : Matrix (Fin n) (Fin n) ℤ} {U : ℕ}
    (hA : EntriesBound A U) : A.trace.natAbs ≤ n * U := by
  calc
    _ ≤ ∑ i, (A i i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i : Fin n, U := Finset.sum_le_sum (fun i _ => hA i i)
    _ = _ := by simp

theorem entriesBound_add_scalar {A : Matrix (Fin n) (Fin n) ℤ} {U V : ℕ}
    (hA : EntriesBound A U) (c : ℤ) (hc : c.natAbs ≤ V) :
    EntriesBound (A + Matrix.scalar (Fin n) c) (U + V) := by
  intro i j
  apply (Int.natAbs_add_le _ _).trans
  apply Nat.add_le_add (hA i j)
  change ((Matrix.diagonal (fun _ : Fin n => c)) i j).natAbs ≤ V
  by_cases h : i = j
  · subst j; simpa using hc
  · simp [Matrix.diagonal_apply_ne _ h]

theorem entriesBound_mono {A : Matrix (Fin n) (Fin n) ℤ} {U V : ℕ}
    (h : EntriesBound A U) (hUV : U ≤ V) : EntriesBound A V :=
  fun i j => (h i j).trans hUV

theorem product_abs_pow (A B : Matrix (Fin n) (Fin n) ℤ) (L E : ℕ)
    (hn : n ≤ L) (hA : EntriesBound A (2^L)) (hB : EntriesBound B (2^E)) :
    EntriesBound (A * B) (2^(2*L+E)) := by
  apply entriesBound_mono (entriesBound_mul hA hB)
  calc
    n * (2^L * 2^E) ≤ 2^L * (2^L * 2^E) :=
      Nat.mul_le_mul_right _ (hn.trans (Nat.le_of_lt L.lt_two_pow_self))
    _ = _ := by simp only [← pow_add]; congr 1; omega

theorem trace_abs_pow (A : Matrix (Fin n) (Fin n) ℤ) (L E : ℕ)
    (hn : n ≤ L) (hA : EntriesBound A (2^E)) :
    A.trace.natAbs ≤ 2^(L+E) := by
  calc
    _ ≤ n * 2^E := trace_abs_le hA
    _ ≤ 2^L * 2^E :=
      Nat.mul_le_mul_right _ (hn.trans (Nat.le_of_lt L.lt_two_pow_self))
    _ = _ := (pow_add _ _ _).symm

theorem faddeevState_abs (A : Matrix (Fin n) (Fin n) ℤ) (L : ℕ)
    (hn : n ≤ L) (hA : EntriesBound A (2^L)) (k : ℕ) :
    EntriesBound (faddeevState A k).1 (2^(4*(L+1)*k)) ∧
      (faddeevState A k).2.natAbs ≤ 2^(4*(L+1)*k) := by
  induction k with
  | zero =>
    constructor
    · intro i j
      simp only [faddeevState, Matrix.one_apply, mul_zero, pow_zero]
      split_ifs <;> simp
    · simp [faddeevState]
  | succ k ih =>
    have hp := product_abs_pow A (faddeevState A k).1 L (4*(L+1)*k) hn hA ih.1
    have ht := trace_abs_pow (A * (faddeevState A k).1) L (2*L+4*(L+1)*k) hn hp
    have hc : (nextCoefficient A (faddeevState A k).1 k).natAbs ≤ 2^(3*L+4*(L+1)*k) := by
      apply (Int.natAbs_ediv_le_natAbs _ _).trans
      simpa only [Int.natAbs_neg, show L+(2*L+4*(L+1)*k)=3*L+4*(L+1)*k by omega] using ht
    have hp' := entriesBound_mono hp (Nat.pow_le_pow_right (by decide)
      (show 2*L+4*(L+1)*k ≤ 3*L+4*(L+1)*k by omega))
    have hsum : 2^(3*L+4*(L+1)*k) + 2^(3*L+4*(L+1)*k) ≤ 2^(4*(L+1)*(k+1)) := by
      calc
        _ = 2^(3*L+4*(L+1)*k+1) := by rw [pow_succ]; omega
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
    constructor
    · exact entriesBound_mono (entriesBound_add_scalar hp' _ hc) hsum
    · exact hc.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

theorem faddeevState_input_abs (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    EntriesBound (faddeevState A k).1 (2^(4*((matrixInput A).length+1)*k)) ∧
      (faddeevState A k).2.natAbs ≤ 2^(4*((matrixInput A).length+1)*k) :=
  faddeevState_abs A _ (dimension_le_input A) (entry_abs_le_input_pow A) k

theorem faddeevState_bitLength (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k ≤ n) :
    (∀ i j, (signedBits ((faddeevState A k).1 i j)).length ≤ 4*((matrixInput A).length+1)^2) ∧
      (signedBits (faddeevState A k).2).length ≤ 4*((matrixInput A).length+1)^2 := by
  obtain ⟨hB,hc⟩ := faddeevState_input_abs A k
  have hn := dimension_le_input A
  have he : 4*((matrixInput A).length+1)*k+2 ≤ 4*((matrixInput A).length+1)^2 := by
    nlinarith
  exact ⟨fun i j => (signedBits_length_of_abs_bound (hB i j)).trans he,
    (signedBits_length_of_abs_bound hc).trans he⟩

end HiddenCircuits.Complexity.DeterminantRuntime
