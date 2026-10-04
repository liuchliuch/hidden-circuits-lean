import HiddenCircuits.Approximation.Initialization.ResidualTest
import HiddenCircuits.Approximation.SamplerRuntime.StepSemantics
import HiddenCircuits.Complexity.BinaryArithmetic.Bits
import HiddenCircuits.Complexity.GraphEncoding

/-! The integer Tutte matrix built from literal little-endian raw
bit slices. Its rational cast is exactly the finite-coin polynomial test. -/
namespace HiddenCircuits.Approximation.Initialization.TutteInteger
open Complexity SamplerRuntime SelfReduction FiniteChains
open scoped Matrix

def number (B : ℕ) (source : BitString) (i : ℕ) : ℕ :=
  BinaryArithmetic.value (TapeRead.takePadded B (source.drop (i*B)))

def matrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : ℕ) (source : BitString) : Matrix (Fin n) (Fin n) ℤ :=
  TuttePolynomial.matrix G (fun i => (number B source i.val : ℤ))

def positive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : ℕ) (source : BitString) : Bool := decide ((matrix G B source).det ≠ 0)

theorem cast_matrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : ℕ) (source : BitString) :
    (Int.castRingHom ℚ).mapMatrix (matrix G B source) =
      TuttePolynomial.matrix G (fun i => (number B source i.val : ℚ)) := by
  ext i j
  by_cases h : G.Adj i j <;> by_cases hij : i < j <;>
    simp [matrix,TuttePolynomial.matrix,h,hij]

theorem positive_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : ℕ) (source : BitString) (h : positive G B source = true) :
    Nonempty (PerfectMatching G) := by
  apply TuttePolynomial.matrix_sound
  rw [←cast_matrix G B source, ←RingHom.map_det]
  change ((matrix G B source).det : ℚ) ≠ 0
  exact_mod_cast (of_decide_eq_true h : (matrix G B source).det ≠ 0)

theorem binary_eq_little (xs : BitString) : BinaryArithmetic.value xs = UnaryDecode.little xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [BinaryArithmetic.value_cons,UnaryDecode.little_cons,ih]
    change (if b then 1 else 0) + 2*UnaryDecode.little xs =
      2*UnaryDecode.little xs + (if b then 1 else 0)
    omega

theorem block_ofFn {q m : ℕ} (r : CoinTape (q*m)) (i : Fin q) :
    TapeRead.takePadded m ((List.ofFn r).drop (i.val*m)) = List.ofFn (splitBlocks q m r i) := by
  have hi : (i.val+1)*m ≤ q*m := Nat.mul_le_mul_right m (by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hi
  rw [TapeRead.prefix_eq_take _ _ (by simp; omega)]
  apply List.ext_getElem
  · simp
    omega
  · intro j hj hj'
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    change r ⟨i.val*m+j,_⟩ = r (finProdFinEquiv (i,⟨j,_⟩))
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem number_ofFn {q m : ℕ} (r : CoinTape (q*m)) (i : Fin q) :
    number m (List.ofFn r) i.val = (tapeNumber m (splitBlocks q m r i)).val := by
  rw [number,block_ofFn,binary_eq_little,UnaryDecode.little_ofFn]

theorem number_prefix {a M B : ℕ} (h : a ≤ M) (r : CoinTape M) (i : ℕ)
    (hi : (i+1)*B ≤ a) :
    number B (List.ofFn r) i = number B (List.ofFn (ResidualTest.takeTape h r)) i := by
  rw [SamplerRuntime.CoinLists.restrict_ofFn]
  unfold number
  simp only [Nat.add_mul,Nat.one_mul] at hi
  rw [TapeRead.prefix_eq_take _ _ (by simp; omega),
    TapeRead.prefix_eq_take _ _ (by simp [Nat.min_eq_left h]; omega)]
  rw [List.drop_take, List.take_take]
  congr 1
  congr 1
  omega

theorem positive_ofFn {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (r : CoinTape (n*n*m)) :
    positive G m (List.ofFn r) = decide
      ((TuttePolynomial.matrix G (TutteCoins.draw (n*n) m r)).det ≠ 0) := by
  unfold positive
  have he : (Int.castRingHom ℚ).mapMatrix (matrix G m (List.ofFn r)) =
      TuttePolynomial.matrix G (TutteCoins.draw (n*n) m r) := by
    rw [cast_matrix]
    congr 1
    funext i
    simp [number_ofFn,TutteCoins.draw]
  rw [←he,←RingHom.map_det]
  change decide ((matrix G m (List.ofFn r)).det ≠ 0) =
    decide (((matrix G m (List.ofFn r)).det : ℚ) ≠ 0)
  simp only [ne_eq, Int.cast_eq_zero]

theorem positive_prefix {n M m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : n*n*m ≤ M) (r : CoinTape M) :
    positive G m (List.ofFn r) = positive G m (List.ofFn (ResidualTest.takeTape h r)) := by
  have he : (fun i : Fin (n*n) => (number m (List.ofFn r) i.val : ℤ)) =
      (fun i : Fin (n*n) => (number m (List.ofFn (ResidualTest.takeTape h r)) i.val : ℤ)) := by
    funext i
    rw [number_prefix h r i.val (Nat.mul_le_mul_right m (by omega))]
  unfold positive matrix
  rw [he]

end HiddenCircuits.Approximation.Initialization.TutteInteger
