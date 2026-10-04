import HiddenCircuits.IntegralTransfers
import Mathlib.Data.Fintype.Powerset

namespace HiddenCircuits
open scoped BigOperators

@[simp] theorem card_state (n q : ℕ) : Fintype.card (State n q) = n.choose q := by
  simp [State]

/-- Uniform entry magnitude, retaining the exponentially large state dimension explicitly. -/
def EntryBound {ι κ : Type*} (M : Matrix ι κ ℚ) (b : ℚ) : Prop := ∀ i j, |M i j| ≤ b

namespace EntryBound
variable {ι κ ν : Type*}
 theorem mono {M : Matrix ι κ ℚ} {b c : ℚ} (h : EntryBound M b) (hbc : b ≤ c) :
    EntryBound M c := fun i j => (h i j).trans hbc
 theorem one [DecidableEq ι] : EntryBound (1 : Matrix ι ι ℚ) 1 := by
  intro i j
  by_cases h:i=j <;> simp [Matrix.one_apply,h]
 theorem neg {M : Matrix ι κ ℚ} {b : ℚ} (h : EntryBound M b) : EntryBound (-M) b := by
  intro i j
  simpa using h i j
 theorem mul [Fintype κ] {M : Matrix ι κ ℚ} {A : Matrix κ ν ℚ} {b c : ℚ}
    (hM : EntryBound M b) (hA : EntryBound A c) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    EntryBound (M*A) (Fintype.card κ * b*c) := by
  intro i j
  calc
    |(M*A) i j| ≤ ∑ k : κ, |M i k * A k j| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : κ, b*c := Finset.sum_le_sum (fun k _ => by
      rw [abs_mul]
      exact mul_le_mul (hM i k) (hA k j) (abs_nonneg _) hb)
    _ = _ := by simp [mul_assoc]

 theorem pow [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℚ} {b : ℚ}
    (hM : EntryBound M b) (hb : 1 ≤ b) : ∀ a,
      EntryBound (M^a) ((((Fintype.card ι : ℚ)+1)*b)^a) := by
  intro a
  induction a with
  | zero => simpa using one
  | succ a ih =>
    rw [pow_succ]
    apply (ih.mul hM (by positivity) (by linarith)).mono
    rw [pow_succ]
    have hp : 0 ≤ (((Fintype.card ι : ℚ)+1)*b)^a := by positivity
    nlinarith

 theorem sum {α : Type*} (s : Finset α) (M : α → Matrix ι κ ℚ) (b : ℚ)
    (h : ∀ k ∈ s, EntryBound (M k) b) : EntryBound (∑ k ∈ s, M k) (s.card*b) := by
  intro i j
  rw [Matrix.sum_apply]
  calc
    |∑ k ∈ s, M k i j| ≤ ∑ k ∈ s, |M k i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ s, b := Finset.sum_le_sum (fun k hk => h k hk i j)
    _ = _ := by simp

 theorem list_prod [Fintype ι] [DecidableEq ι] (w : List (Matrix ι ι ℚ)) (b : ℚ)
    (hb : 1 ≤ b) (h : ∀ M ∈ w, EntryBound M b) :
    EntryBound w.prod ((((Fintype.card ι : ℚ)+1)*b)^w.length) := by
  induction w with
  | nil => simpa using one
  | cons M w ih =>
    have hM := h M (by simp)
    have hw := ih (fun A hA => h A (by simp [hA]))
    simp only [List.prod_cons, List.length_cons]
    apply (hM.mul hw (by linarith) (by positivity)).mono
    rw [pow_succ]
    have hp : 0 ≤ (((Fintype.card ι : ℚ)+1)*b)^w.length := by positivity
    nlinarith
end EntryBound

/-- A zero-one cut permanent is bounded by the number of bijections. -/
theorem compound_entry_bound {n q : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ i j, M i j = 0 ∨ M i j = 1) : EntryBound (compound (q:=q) M) q.factorial := by
  intro S T
  unfold compound Matrix.permanent
  calc
    |∑ σ : Equiv.Perm (Fin q), ∏ j : Fin q, M (S.track (σ j)) (T.track j)|
        ≤ ∑ σ : Equiv.Perm (Fin q), |∏ j : Fin q, M (S.track (σ j)) (T.track j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin q), (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Finset.abs_prod]
      apply Finset.prod_le_one
      · intro j _; exact abs_nonneg _
      · intro j _
        rcases h (S.track (σ j)) (T.track j) with hz | ho
        · simp [hz]
        · simp [ho]
    _ = _ := by simp [Fintype.card_perm]

 theorem upper_entry_bound (n q : ℕ) : EntryBound (compound (q:=q) (upper n)) q.factorial :=
  compound_entry_bound _ (fun i j => by unfold upper; split_ifs <;> simp)

 theorem upper_difference_bound (n q : ℕ) :
    EntryBound (compound (q:=q) (upper n)-1) q.factorial := by
  intro S T
  by_cases h:S=T
  · subst T; simpa using (show (0:ℚ) ≤ q.factorial from by positivity)
  · simpa [Matrix.one_apply,h] using upper_entry_bound n q S T

def inverseMagnitude (n q : ℕ) : ℕ :=
  (q*(n-q)+1) * (((n.choose q)+1)*q.factorial)^(q*(n-q))

theorem upperInverse_entry_bound (n q : ℕ) :
    EntryBound (upperInverse n q) (inverseMagnitude n q) := by
  have hb : (1:ℚ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hbase : (1:ℚ) ≤ ((n.choose q : ℚ)+1)*q.factorial := by nlinarith [show (0:ℚ) ≤ n.choose q from by positivity]
  unfold upperInverse inverseSeries
  have hs := EntryBound.sum (Finset.range (q*(n-q)+1))
    (fun a => (-(compound (q:=q) (upper n)-1))^a)
    ((((n.choose q : ℚ)+1)*q.factorial)^(q*(n-q))) (by
      intro a ha
      have hh := (upper_difference_bound n q).neg.pow hb a
      simp only [card_state] at hh
      apply hh.mono
      exact pow_le_pow_right₀ hbase (Nat.le_of_lt_succ (Finset.mem_range.mp ha)))
  simpa [inverseMagnitude, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using hs

def letterMagnitude (p : ℕ) : ℕ :=
  (2*p).choose p * p.factorial * inverseMagnitude (2*p) p

theorem rise_entry_bound (p : ℕ) (i : Fin (2*p-1)) :
    EntryBound (rise (2*p) p i) (letterMagnitude p) := by
  have hcut := compound_entry_bound (q:=p) (addedCut i) (by
    intro a b; unfold addedCut upper; split_ifs <;> simp)
  have h := hcut.mul (upperInverse_entry_bound (2*p) p) (by positivity) (by positivity)
  simpa [rise,letterMagnitude,card_state,Nat.cast_mul] using h

theorem drop_entry_bound (p : ℕ) (i : Fin (2*p-1)) :
    EntryBound (drop (2*p) p i) (letterMagnitude p) := by
  have hcut := compound_entry_bound (q:=p) (deletedCut i) (by
    intro a b; unfold deletedCut upper; split_ifs <;> simp)
  have h := hcut.mul (upperInverse_entry_bound (2*p) p) (by positivity) (by positivity)
  simpa [drop,letterMagnitude,card_state,Nat.cast_mul] using h

theorem letter_entry_bound (p : ℕ) (l : Letter (2*p)) :
    EntryBound (l.matrix p) (letterMagnitude p) := by
  have hp : 2*p-p=p := by omega
  cases l with
  | mk kind i =>
    cases kind with
    | R => exact rise_entry_bound p i
    | D => exact drop_entry_bound p i
    | B =>
      intro S T
      change |rise (2*p) (2*p-p) i T.complement S.complement| ≤ _
      have h : ∀ q, q=p → EntryBound (rise (2*p) q i) (letterMagnitude p) := by
        intro q hq
        subst q
        exact rise_entry_bound p i
      exact h _ hp T.complement S.complement
    | E =>
      intro S T
      change |drop (2*p) (2*p-p) i T.complement S.complement| ≤ _
      have h : ∀ q, q=p → EntryBound (drop (2*p) q i) (letterMagnitude p) := by
        intro q hq
        subst q
        exact drop_entry_bound p i
      exact h _ hp T.complement S.complement

/-- Explicit magnitude bound on the actual implicit WordEval matrix. -/
theorem word_entry_bound (p : ℕ) (w : List (Letter (2*p))) :
    EntryBound (wordMatrix p w) ((((2*p).choose p + 1)*max 1 (letterMagnitude p) : ℕ)^w.length) := by
  have hh := EntryBound.list_prod (w.map (Letter.matrix p)) (max 1 (letterMagnitude p))
    (by exact_mod_cast le_max_left 1 (letterMagnitude p)) (by
      intro M hM
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp hM
      exact (letter_entry_bound p l).mono (by exact_mod_cast le_max_right 1 (letterMagnitude p)))
  simpa [wordMatrix,card_state,Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh

end HiddenCircuits
