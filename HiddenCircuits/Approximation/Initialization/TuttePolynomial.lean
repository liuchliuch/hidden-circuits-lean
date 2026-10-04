import HiddenCircuits.Approximation.Initialization.SkewTutte
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing

/-! The skew Tutte determinant polynomial. Its degree is at most the
vertex count; a genuine matching supplies a concrete nonsingular 0/1 edge
specialization, proving nonvanishing without assuming a coefficient formula. -/
namespace HiddenCircuits.Approximation.Initialization.TuttePolynomial
open scoped BigOperators Matrix
open Matrix MvPolynomial

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def index (i j : Fin n) : Fin (n*n) := finProdFinEquiv (i,j)

def matrix {R : Type*} [CommRing R] (x : Fin (n*n) → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if G.Adj i j then if i < j then x (index i j) else -x (index j i) else 0

theorem matrix_skew {R : Type*} [CommRing R] (x : Fin (n*n) → R) :
    (matrix G x).transpose = -matrix G x := by
  ext i j
  by_cases ha : G.Adj i j
  · have hb := ha.symm
    have hn := ha.ne
    by_cases hij : i < j
    · have hji : ¬j < i := not_lt_of_ge hij.le
      simp [matrix, ha, hb, hij, hji]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) hn.symm
      simp [matrix, ha, hb, hij, hji]
  · have hb : ¬G.Adj j i := fun h => ha h.symm
    simp [matrix, ha, hb]

theorem matrix_supported {R : Type*} [CommRing R] (x : Fin (n*n) → R)
    (i j : Fin n) (h : ¬G.Adj i j) : matrix G x i j = 0 := by simp [matrix, h]

theorem matrix_sound (x : Fin (n*n) → ℚ) (h : (matrix G x).det ≠ 0) :
    Nonempty (PerfectMatching G) :=
  SkewTutte.perfectMatching_of_det_ne_zero G (matrix G x) (matrix_skew G x)
    (matrix_supported G x) h

noncomputable def polynomial : MvPolynomial (Fin (n*n)) ℚ := (matrix G (X : Fin (n*n) → MvPolynomial (Fin (n*n)) ℚ)).det

theorem eval_polynomial (x : Fin (n*n) → ℚ) :
    eval x (polynomial G) = (matrix G x).det := by
  rw [polynomial, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply]
  by_cases h : G.Adj i j <;> by_cases hij : i < j <;>
    simp [matrix, h, hij]

def matchingValues (P : PerfectPartner G) (e : Fin (n*n)) : ℚ :=
  if P.val (finProdFinEquiv.symm e).1 = (finProdFinEquiv.symm e).2 then 1 else 0

theorem matching_entry (P : PerfectPartner G) (i j : Fin n) :
    matrix G (matchingValues G P) i j =
      if P.val i = j then (if i < j then 1 else -1) else 0 := by
  have hji : P.val j = i ↔ P.val i = j := by
    constructor <;> intro h
    · rw [←h, P.property.1]
    · rw [←h, P.property.1]
  by_cases hp : P.val i = j
  · have ha : G.Adj i j := hp ▸ P.property.2 i
    simp [matrix, matchingValues, index, hp, ha, hji]
  · by_cases ha : G.Adj i j <;>
      simp [matrix, matchingValues, index, hp, ha, hji]

theorem matching_mulVec (P : PerfectPartner G) (x : Fin n → ℚ) (i : Fin n) :
    (matrix G (matchingValues G P) *ᵥ x) i =
      (if i < P.val i then 1 else -1) * x (P.val i) := by
  classical
  simp only [Matrix.mulVec, dotProduct, matching_entry]
  rw [Finset.sum_eq_single (P.val i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem matching_det_ne_zero (P : PerfectPartner G) :
    (matrix G (matchingValues G P)).det ≠ 0 := by
  intro h
  obtain ⟨x, hx, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hx
  funext i
  have hh := congrFun hm (P.val i)
  rw [matching_mulVec, P.property.1] at hh
  split_ifs at hh <;> simpa using hh

theorem polynomial_ne_zero (hG : Nonempty (PerfectMatching G)) : polynomial G ≠ 0 := by
  obtain ⟨P⟩ := hG
  intro h
  have hh := eval_polynomial G (matchingValues G P.toPartner)
  rw [h, map_zero] at hh
  exact matching_det_ne_zero G P.toPartner hh.symm

theorem entry_degree (i j : Fin n) : (matrix G (X : Fin (n*n) → MvPolynomial (Fin (n*n)) ℚ) i j).totalDegree ≤ 1 := by
  by_cases h : G.Adj i j <;> by_cases hij : i < j <;>
    simp [matrix, h, hij, totalDegree_neg]

theorem polynomial_degree : (polynomial G).totalDegree ≤ n := by
  classical
  rw [polynomial, Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro σ _
  have hconstant : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin (n*n)) ℚ)).totalDegree = 0 := by
    have he : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin (n*n)) ℚ) =
        C ((Equiv.Perm.sign σ : ℤ) : ℚ) := by simp
    rw [he, totalDegree_C]
  calc
    _ ≤ (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin (n*n)) ℚ)).totalDegree +
        (∏ i, matrix G (X : Fin (n*n) → MvPolynomial (Fin (n*n)) ℚ) (σ i) i).totalDegree := totalDegree_mul _ _
    _ = (∏ i, matrix G (X : Fin (n*n) → MvPolynomial (Fin (n*n)) ℚ) (σ i) i).totalDegree := by rw [hconstant, zero_add]
    _ ≤ ∑ i, (matrix G (X : Fin (n*n) → MvPolynomial (Fin (n*n)) ℚ) (σ i) i).totalDegree := totalDegree_finset_prod _ _
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => entry_degree G (σ i) i)
    _ = n := by simp

end HiddenCircuits.Approximation.Initialization.TuttePolynomial
