import HiddenCircuits.BlockWords
import HiddenCircuits.FilterTheorem

namespace HiddenCircuits
open scoped Kronecker BigOperators

/-- Recursively grouped consecutive tracks, definitionally compatible with actual state joins. -/
def blockWidth : ℕ → ℕ
  | 0 => 0
  | k+1 => 4+blockWidth k

@[simp] theorem blockWidth_eq (k : ℕ) : blockWidth k = 4*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [blockWidth,ih]; omega

/-- Literal concatenation of translated twenty-letter filters, in left-to-right block order. -/
def globalFilterWord : (k : ℕ) → List (Letter (blockWidth k))
  | 0 => []
  | k+1 => (filterWord.map (Letter.inLeft (blockWidth k))) ++
      ((globalFilterWord k).map (Letter.inRight 4))

/-- This is the actual scalar-normalized global word of Section 5. -/
def globalFilter (k q : ℕ) : Matrix (State (blockWidth k) q) (State (blockWidth k) q) ℚ :=
  ((1/64 : ℚ)^k) • wordMatrix q (globalFilterWord k)

@[simp] theorem globalFilterWord_length (k : ℕ) : (globalFilterWord k).length = 20*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [globalFilterWord,ih]; omega

@[simp] theorem blockRestrict_smul {a b u v : ℕ} (c : ℚ)
    (M : Matrix (State (a+b) (u+v)) (State (a+b) (u+v)) ℚ) :
    blockRestrict (c • M) = c • blockRestrict M := rfl

/-- The first diagonal cut of the concrete global filter factors, by no-return and actual normalization. -/
theorem blockRestrict_globalFilter (k u v : ℕ) :
    blockRestrict (globalFilter (k+1) (u+v)) = localFilter u ⊗ₖ globalFilter k v := by
  unfold globalFilter
  rw [blockRestrict_smul,globalFilterWord,wordMatrix_append]
  rw [blockRestrict_mul _ _
    (word_prefix_outside _ 4 (by
      intro l hl
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp hl
      exact l.left_boundary))
    (word_prefix_outside _ 4 (by
      intro l hl
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp hl
      exact l.right_boundary))]
  rw [blockRestrict_word_left,blockRestrict_word_right,← Matrix.mul_kronecker_mul,mul_one,one_mul]
  rw [localFilter,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,pow_succ']

/-- A tuple of genuine four-track fixed-particle states. -/
def BlockStates : List ℕ → Type
  | [] => PUnit
  | q::qs => State 4 q × BlockStates qs

instance blockStatesDecidableEq : (qs : List ℕ) → DecidableEq (BlockStates qs)
  | [] => inferInstanceAs (DecidableEq PUnit)
  | _::qs => by
      letI := blockStatesDecidableEq qs
      exact inferInstanceAs (DecidableEq (_ × _))

instance blockStatesFintype : (qs : List ℕ) → Fintype (BlockStates qs)
  | [] => inferInstanceAs (Fintype PUnit)
  | _::qs => by
      letI := blockStatesFintype qs
      exact inferInstanceAs (Fintype (_ × _))

/-- Concatenation maps tuple coordinates to actual subset states. -/
def joinBlocks : (qs : List ℕ) → BlockStates qs → State (blockWidth qs.length) qs.sum
  | [], _ => ⟨∅,rfl⟩
  | _::qs, S => State.join S.1 (joinBlocks qs S.2)

/-- The actual tensor of isolated filters on a fixed count vector. -/
def filterTensor : (qs : List ℕ) → Matrix (BlockStates qs) (BlockStates qs) ℚ
  | [] => 1
  | q::qs => localFilter q ⊗ₖ filterTensor qs

/-- Exact diagonal-block formula for every particle-count vector, not an assumed tensor action. -/
theorem globalFilter_diagonal (qs : List ℕ) :
    (globalFilter qs.length qs.sum).submatrix (joinBlocks qs) (joinBlocks qs) = filterTensor qs := by
  induction qs with
  | nil =>
    ext S T
    cases S
    cases T
    simp [globalFilter,globalFilterWord,filterTensor,joinBlocks,Matrix.one_apply]
  | cons q qs ih =>
    ext S T
    have h := congrFun (congrFun (blockRestrict_globalFilter qs.length q qs.sum)
      (S.1,joinBlocks qs S.2)) (T.1,joinBlocks qs T.2)
    have hh := congrFun (congrFun ih S.2) T.2
    change globalFilter _ _ _ _ = filterTensor qs S.2 T.2 at hh
    simpa only [blockRestrict,Matrix.submatrix_apply,joinBlocks,List.length_cons,List.sum_cons,
      filterTensor,Matrix.kronecker_apply,Matrix.kroneckerMap_apply,hh] using h

/-- If every block contains at least two particles, the total is at least twice the block count. -/
theorem two_length_le_sum (qs : List ℕ) (h : ∀ q ∈ qs, 2 ≤ q) : 2*qs.length ≤ qs.sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hq := h q (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons,List.sum_cons]
    omega

/-- At fixed average two, a different count vector has a deficient block. -/
theorem exists_low_count (qs : List ℕ) (hs : qs.sum = 2*qs.length)
    (hne : qs ≠ List.replicate qs.length 2) : ∃ q ∈ qs, q<2 := by
  by_contra h
  have hlo : ∀ q ∈ qs, 2 ≤ q := by
    intro q hq
    by_contra hh
    exact h ⟨q,hq,by omega⟩
  apply hne
  clear hne h
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hq := hlo q (by simp)
    have ht : ∀ x ∈ qs, 2 ≤ x := fun x hx => hlo x (by simp [hx])
    have hs' := two_length_le_sum qs ht
    simp only [List.sum_cons,List.length_cons] at hs
    have he : q=2 := by omega
    subst q
    have ih' := ih (by omega) ht
    simpa only [List.length_cons,List.replicate_succ] using congrArg (List.cons 2) ih'

/-- One deficient block annihilates the entire actual diagonal tensor. -/
theorem filterTensor_zero_of_low (qs : List ℕ) (h : ∃ q ∈ qs, q<2) : filterTensor qs = 0 := by
  induction qs with
  | nil => simpa using h
  | cons q qs ih =>
    obtain ⟨x,hx,hlt⟩ := h
    simp only [List.mem_cons] at hx
    rcases hx with he | hx
    · subst x
      have hq : q=0 ∨ q=1 := by omega
      rcases hq with rfl | rfl <;>
        simp [filterTensor,localFilter_zero,localFilter_one]
    · simp [filterTensor,ih ⟨x,hx,hlt⟩]

/-- All nonbalanced diagonal count blocks vanish in the half-filled space. -/
theorem globalFilter_diagonal_zero (qs : List ℕ) (hs : qs.sum=2*qs.length)
    (hne : qs ≠ List.replicate qs.length 2) :
    (globalFilter qs.length qs.sum).submatrix (joinBlocks qs) (joinBlocks qs) = 0 := by
  rw [globalFilter_diagonal]
  exact filterTensor_zero_of_low qs (exists_low_count qs hs hne)

/-- The unique balanced diagonal block is genuinely idempotent. -/
theorem filterTensor_balanced_idempotent (k : ℕ) :
    filterTensor (List.replicate k 2) * filterTensor (List.replicate k 2) =
      filterTensor (List.replicate k 2) := by
  induction k with
  | zero => simp [filterTensor]
  | succ k ih =>
    simp only [List.replicate_succ,filterTensor]
    rw [← Matrix.mul_kronecker_mul,localFilter_idempotent,ih]

end HiddenCircuits
