import HiddenCircuits.PairedSampling
import HiddenCircuits.Complexity.Interpolation

namespace HiddenCircuits
open scoped BigOperators
open Polynomial

/-- An entrywise degree bound for a concrete matrix of univariate rational polynomials. -/
def PolynomialMatrixDegree {ι : Type*} (M : Matrix ι ι ℚ[X]) (d : ℕ) : Prop :=
  ∀ i j, (M i j).natDegree≤d

namespace PolynomialMatrixDegree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
 theorem one : PolynomialMatrixDegree (1 : Matrix ι ι ℚ[X]) 0 := by
  intro i j
  by_cases h:i=j <;> simp [Matrix.one_apply,h]
 theorem constant (M : Matrix ι ι ℚ) : PolynomialMatrixDegree (constantMatrix M) 0 := by
  intro i j
  simp [constantMatrix]
 theorem mul {M N : Matrix ι ι ℚ[X]} {d e : ℕ}
    (hM : PolynomialMatrixDegree M d) (hN : PolynomialMatrixDegree N e) :
    PolynomialMatrixDegree (M*N) (d+e) := by
  intro i j
  change (∑ k, M i k * N k j).natDegree≤d+e
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact Polynomial.natDegree_mul_le_of_le (hM i k) (hN k j)
end PolynomialMatrixDegree

 theorem letterPairPolynomial_degree {p : ℕ} (l : Letter (2*p)) :
    PolynomialMatrixDegree (letterPairPolynomial l) (p^2) := by
  have hb : PolynomialMatrixDegree (backgroundPolynomial p) (p^2) :=
    unipotentPolynomial_degree _ _
  cases l with
  | mk kind i =>
    cases kind with
    | R => simpa only [letterPairPolynomial,Nat.zero_add] using (PolynomialMatrixDegree.constant _).mul hb
    | D => simpa only [letterPairPolynomial,Nat.zero_add] using (PolynomialMatrixDegree.constant _).mul hb
    | B => simpa only [letterPairPolynomial,Nat.add_zero] using hb.mul (PolynomialMatrixDegree.constant _)
    | E => simpa only [letterPairPolynomial,Nat.add_zero] using hb.mul (PolynomialMatrixDegree.constant _)

/-- A shared parameter makes the degree linear in the number of input letters. -/
theorem wordPairPolynomial_degree {p : ℕ} (w : List (Letter (2*p))) :
    PolynomialMatrixDegree (wordPairPolynomial w) (w.length*p^2) := by
  induction w with
  | nil => simpa only [wordPairPolynomial,List.map_nil,List.prod_nil,List.length_nil,Nat.zero_mul] using PolynomialMatrixDegree.one
  | cons l w ih =>
    have hd := (letterPairPolynomial_degree l).mul ih
    simpa only [wordPairPolynomial,List.map_cons,List.prod_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using hd

/-- Explicit postprocessing of exactly gp²+1 actual nonnegative paired-word samples. -/
noncomputable def recoverWordFromPairs {p : ℕ} (w : List (Letter (2*p)))
    (S T : State (2*p) p) : ℚ :=
  (Complexity.interpolateValues (w.length*p^2)
    (fun t => pairWordMatrix (sampleWord w t.val) S T)).eval (-1)

/-- The exact algebraic recovery identity behind Lemma3.3, including the actual allowed sample words.
This is the identity; source encoding and executable rational runtime remain separate obligations. -/
theorem recoverWordFromPairs_correct {p : ℕ} (w : List (Letter (2*p))) (S T : State (2*p) p) :
    recoverWordFromPairs w S T = wordMatrix p w S T := by
  have hi := Complexity.interpolateValues_correct (w.length*p^2) (wordPairPolynomial w S T)
    (wordPairPolynomial_degree w S T)
  have hn : (fun t : Fin (w.length*p^2+1) =>
      (wordPairPolynomial w S T).eval (Complexity.interpolationNode t)) =
    (fun t => pairWordMatrix (sampleWord w t.val) S T) := by
    funext t
    exact congrFun (congrFun (wordPairPolynomial_nat w t.val) S) T
  rw [hn] at hi
  unfold recoverWordFromPairs
  rw [hi]
  exact congrFun (congrFun (wordPairPolynomial_neg_one w) S) T

 theorem pairedQuery_count {p : ℕ} (w : List (Letter (2*p))) :
    Fintype.card (Fin (w.length*p^2+1))=w.length*p^2+1 := Fintype.card_fin _

/-- Every submitted sample has the stated polynomial number of pairs. -/
theorem pairedQuery_size {p : ℕ} (w : List (Letter (2*p))) (t : Fin (w.length*p^2+1)) :
    (sampleWord w t.val).length=w.length*(t.val+1) ∧
    (sampleWord w t.val).length≤w.length*(w.length*p^2+1) := by
  rw [sampleWord_length]
  exact ⟨rfl,Nat.mul_le_mul_left _ (by have ht := t.isLt; omega)⟩

/-- A nonempty input word always gives an admissible nonempty pair sequence at every node. -/
theorem pairedQuery_nonempty {p : ℕ} (w : List (Letter (2*p))) (hw : w≠[]) (t : ℕ) :
    sampleWord w t ≠ [] := by
  have hl : w.length ≠ 0 := by
    cases w with
    | nil => exact False.elim (hw rfl)
    | cons l w => simp
  have hp : w.length*(t+1)≠0 := Nat.mul_ne_zero hl (by omega)
  intro hz
  exact hp ((sampleWord_length w t).symm.trans (congrArg List.length hz))

end HiddenCircuits
