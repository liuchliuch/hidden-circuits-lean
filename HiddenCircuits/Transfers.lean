import HiddenCircuits.MatrixPotential
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Finset.Sort

/-! Actual fixed-cardinality subset states and permanental compounds from Section 3. -/
namespace HiddenCircuits
open scoped BigOperators

/-- The states are precisely the `q`-element subsets of the `n` ordered tracks. -/
def State (n q : ℕ) := {s : Finset (Fin n) // s.card = q}
  deriving DecidableEq, Fintype

namespace State
variable {n q : ℕ}

def track (S : State n q) : Fin q ↪o Fin n := S.val.orderEmbOfFin S.property

def weight (S : State n q) : ℕ := ∑ j : Fin q, (S.track j).val

@[simp] theorem image_track (S : State n q) : Finset.univ.image S.track = S.val :=
  Finset.image_orderEmbOfFin_univ _ _

 theorem ext_track_image (S T : State n q)
    (h : Finset.univ.image S.track = Finset.univ.image T.track) : S = T := by
  apply Subtype.ext
  simpa using h

end State

/-- This is the permanent, without determinant signs, of the ordered selected submatrix. -/
def compound {n q : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (State n q) (State n q) ℚ :=
  fun S T => Matrix.permanent (M.submatrix S.track T.track)

/-- The unperturbed upper-triangular cut; a simple zero-one cut matrix. -/
def upper (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j => if i ≤ j then 1 else 0

/-- Adding exactly the allowed subdiagonal edge. -/
def addedCut {n : ℕ} (i : Fin (n - 1)) : Matrix (Fin n) (Fin n) ℚ :=
  fun a b => if a.val = i.val + 1 ∧ b.val = i.val then 1 else upper n a b

/-- Removing exactly the allowed diagonal edge. -/
def deletedCut {n : ℕ} (i : Fin (n - 1)) : Matrix (Fin n) (Fin n) ℚ :=
  fun a b => if a.val = i.val ∧ b.val = i.val then 0 else upper n a b

/-- A nonzero upper-cut permanent term has a coordinatewise nondecreasing bijection. -/
theorem upper_term_nonzero_iff {n q : ℕ} (S T : State n q) (σ : Equiv.Perm (Fin q)) :
    (∏ j : Fin q, upper n (S.track (σ j)) (T.track j)) ≠ 0 ↔
      ∀ j, S.track (σ j) ≤ T.track j := by
  simp [upper, Finset.prod_ne_zero_iff]

 theorem term_weight_le {n q : ℕ} (S T : State n q) (σ : Equiv.Perm (Fin q))
    (h : ∀ j, S.track (σ j) ≤ T.track j) : S.weight ≤ T.weight := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => (show (S.track (σ j)).val ≤ (T.track j).val from h j))
  rw [Equiv.sum_comp σ (fun j => (S.track j).val)] at hs
  exact hs

/-- Equality in the potential bound forces equality of the selected subset states. -/
theorem term_weight_eq_states {n q : ℕ} (S T : State n q) (σ : Equiv.Perm (Fin q))
    (h : ∀ j, S.track (σ j) ≤ T.track j) (heq : S.weight = T.weight) : S = T := by
  have hs : (∑ j : Fin q, (S.track (σ j)).val) = ∑ j : Fin q, (T.track j).val := by
    rw [Equiv.sum_comp σ (fun j => (S.track j).val)]
    exact heq
  have he := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) => (show (S.track (σ j)).val ≤ (T.track j).val from h j))).mp hs
  apply State.ext_track_image
  apply Finset.ext
  intro a
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨σ.symm j, ?_⟩
    have hh : S.track (σ (σ.symm j)) = T.track (σ.symm j) := Fin.ext (he _ (Finset.mem_univ _))
    simpa using hh.symm
  · rintro ⟨j, rfl⟩
    exact ⟨σ j, Fin.ext (he _ (Finset.mem_univ _))⟩

 theorem compound_upper_weight_le {n q : ℕ} (S T : State n q)
    (h : compound (upper n) S T ≠ 0) : S.weight ≤ T.weight := by
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact term_weight_le S T σ ((upper_term_nonzero_iff S T σ).mp hσ)

 theorem compound_upper_eq_states {n q : ℕ} (S T : State n q)
    (h : compound (upper n) S T ≠ 0) (heq : S.weight = T.weight) : S = T := by
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact term_weight_eq_states S T σ ((upper_term_nonzero_iff S T σ).mp hσ) heq

@[simp] theorem compound_upper_self {n q : ℕ} (S : State n q) :
    compound (upper n) S S = 1 := by
  unfold compound Matrix.permanent
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin q))]
  · simp [upper, Matrix.submatrix]
  · intro σ _ hσ
    by_contra hne
    have hle := (upper_term_nonzero_iff S S σ).mp hne
    have hs : (∑ j : Fin q, (S.track (σ j)).val) = ∑ j : Fin q, (S.track j).val := by
      exact Equiv.sum_comp σ (fun j => (S.track j).val)
    have he := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) => (show (S.track (σ j)).val ≤ (S.track j).val from hle j))).mp hs
    apply hσ
    apply Equiv.ext
    intro j
    exact S.track.injective (Fin.ext (he j (Finset.mem_univ j)))
  · simp

 theorem compound_upper_sub_one_support {n q : ℕ} (S T : State n q)
    (h : (compound (upper n) - 1) S T ≠ 0) : S.weight + 1 ≤ T.weight := by
  by_cases heq : S = T
  · subst T
    simp at h
  have hentry : compound (upper n) S T ≠ 0 := by simpa [Matrix.one_apply, heq] using h
  have hle := compound_upper_weight_le S T hentry
  have hne : S.weight ≠ T.weight := fun hw => heq (compound_upper_eq_states S T hentry hw)
  omega

/-- An increasing injection of finite ordinal tracks can only move an index upward. -/
theorem orderEmb_index_le {n q : ℕ} (f : Fin q ↪o Fin n) (j : Fin q) :
    j.val ≤ (f j).val := by
  have haux : ∀ k (hk : k < q), k ≤ (f ⟨k, hk⟩).val := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < q := by omega
      have h₁ := ih hk'
      have h₂ := f.strictMono (show (⟨k, hk'⟩ : Fin q) < ⟨k+1, hk⟩ from by simp)
      change (f ⟨k, hk'⟩).val < (f ⟨k+1, hk⟩).val at h₂
      omega
  exact haux j.val j.isLt

 theorem orderEmb_index_upper {n q : ℕ} (f : Fin q ↪o Fin n) (j : Fin q) :
    (f j).val ≤ n - q + j.val := by
  let g : Fin q ↪o Fin n := OrderEmbedding.ofStrictMono
    (fun i => (f i.rev).rev) (by
      intro a b h
      exact Fin.rev_lt_rev.mpr (f.strictMono (Fin.rev_lt_rev.mpr h)))
  have hb := orderEmb_index_le g j.rev
  change j.rev.val ≤ ((f (j.rev.rev)).rev).val at hb
  simp only [Fin.rev_rev, Fin.val_rev] at hb
  have hj := j.isLt
  have hf := (f j).isLt
  omega

/-- The minimum potential, expressed without truncated division. -/
def minWeight (q : ℕ) : ℕ := ∑ j : Fin q, j.val

 theorem state_weight_lower {n q : ℕ} (S : State n q) : minWeight q ≤ S.weight :=
  Finset.sum_le_sum (fun j _ => orderEmb_index_le S.track j)

 theorem state_weight_upper {n q : ℕ} (S : State n q) :
    S.weight ≤ minWeight q + q * (n - q) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => orderEmb_index_upper S.track j)
  simpa [State.weight, minWeight, Finset.sum_add_distrib, Nat.mul_comm, Nat.add_comm] using h

/-- The exact polynomial nilpotence bound, valid at every particle number including 0. -/
theorem compound_upper_nilpotent (n q : ℕ) :
    (compound (q := q) (upper n) - 1) ^ (q * (n - q) + 1) = 0 :=
  potential_nilpotent _ State.weight (minWeight q) (q * (n - q))
    (fun S T => compound_upper_sub_one_support S T)
    state_weight_lower state_weight_upper

/-- Integral finite-series inverse of the unperturbed permanental compound. -/
def upperInverse (n q : ℕ) : Matrix (State n q) (State n q) ℚ :=
  inverseSeries (compound (upper n) - 1) (q * (n - q))

@[simp] theorem upperInverse_mul (n q : ℕ) :
    upperInverse n q * compound (upper n) = 1 := by
  have h := inverseSeries_mul (compound (q := q) (upper n) - 1) (q * (n - q))
    (compound_upper_nilpotent n q)
  simpa [upperInverse, add_sub_cancel_left] using h

@[simp] theorem mul_upperInverse (n q : ℕ) :
    compound (upper n) * upperInverse n q = 1 := by
  have h := mul_inverseSeries (compound (q := q) (upper n) - 1) (q * (n - q))
    (compound_upper_nilpotent n q)
  simpa [upperInverse, add_sub_cancel_left] using h

end HiddenCircuits

namespace HiddenCircuits
namespace State
/-- Complement stays in the complementary particle-number sector. -/
def complement {n q : ℕ} (S : State n q) : State n (n - q) :=
  ⟨S.valᶜ, by simp [Finset.card_compl, S.property]⟩

@[simp] theorem complement_val {n q : ℕ} (S : State n q) :
    S.complement.val = S.valᶜ := rfl
end State

/-- The four normalized operations of equations (3.2) and (3.3), with no locality assumed. -/
inductive LetterKind where
  | R | D | B | E
  deriving DecidableEq, Fintype, Repr

structure Letter (n : ℕ) where
  kind : LetterKind
  index : Fin (n - 1)
  deriving DecidableEq, Fintype

def rise (n q : ℕ) (i : Fin (n - 1)) : Matrix (State n q) (State n q) ℚ :=
  compound (addedCut i) * upperInverse n q

def drop (n q : ℕ) (i : Fin (n - 1)) : Matrix (State n q) (State n q) ℚ :=
  compound (deletedCut i) * upperInverse n q

def dualRise (n q : ℕ) (i : Fin (n - 1)) : Matrix (State n q) (State n q) ℚ :=
  fun S T => rise n (n - q) i T.complement S.complement

def dualDrop (n q : ℕ) (i : Fin (n - 1)) : Matrix (State n q) (State n q) ℚ :=
  fun S T => drop n (n - q) i T.complement S.complement

def Letter.matrix {n : ℕ} (q : ℕ) (l : Letter n) : Matrix (State n q) (State n q) ℚ :=
  match l.kind with
  | .R => rise n q l.index
  | .D => drop n q l.index
  | .B => dualRise n q l.index
  | .E => dualDrop n q l.index

/-- A listed word, with row-vector left-to-right multiplication and empty word the identity. -/
def wordMatrix {n : ℕ} (q : ℕ) (w : List (Letter n)) : Matrix (State n q) (State n q) ℚ :=
  (w.map (Letter.matrix q)).prod

@[simp] theorem wordMatrix_nil (n q : ℕ) : wordMatrix (n := n) q [] = 1 := rfl

@[simp] theorem wordMatrix_cons {n q : ℕ} (l : Letter n) (w : List (Letter n)) :
    wordMatrix q (l :: w) = l.matrix q * wordMatrix q w := rfl

@[simp] theorem wordMatrix_append {n q : ℕ} (w v : List (Letter n)) :
    wordMatrix q (w ++ v) = wordMatrix q w * wordMatrix q v := by
  simp [wordMatrix, List.map_append, List.prod_append]

/-- The exact input type of WordEval: positive half filling and explicit subset boundaries. -/
structure WordInstance where
  particles : ℕ
  positive : 0 < particles
  source : State (2 * particles) particles
  target : State (2 * particles) particles
  word : List (Letter (2 * particles))

def WordInstance.value (w : WordInstance) : ℚ :=
  wordMatrix w.particles w.word w.source w.target

end HiddenCircuits
