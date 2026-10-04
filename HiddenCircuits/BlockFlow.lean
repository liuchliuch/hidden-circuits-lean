import HiddenCircuits.FixedPrefix
import HiddenCircuits.BlockWords

/-! Actual occupied-track counts and no-return flow for a consecutive middle block. -/
namespace HiddenCircuits
open scoped BigOperators
namespace State

/-- Number of selected tracks in the interval `[a,a+b)`. -/
def blockCount {n q : ℕ} (S : State n q) (a b : ℕ) : ℕ :=
  (S.val.filter (fun x => a ≤ x.val ∧ x.val < a+b)).card

 theorem blockCount_sum {n q : ℕ} (S : State n q) (a b : ℕ) :
    S.blockCount a b = ∑ x ∈ S.val, if a ≤ x.val ∧ x.val < a+b then 1 else 0 := by
  simp only [blockCount,Finset.sum_boole,Nat.cast_id]

/-- The actual block count is the increment of the two prefix counts. -/
theorem prefix_add_blockCount {n q : ℕ} (S : State n q) (a b : ℕ) :
    S.prefixCount a + S.blockCount a b = S.prefixCount (a+b) := by
  rw [blockCount_sum]
  simp only [prefixCount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> omega

 theorem blockCount_eq_prefix_sub {n q : ℕ} (S : State n q) (a b : ℕ) :
    S.blockCount a b = S.prefixCount (a+b) - S.prefixCount a := by
  have h := S.prefix_add_blockCount a b
  omega

 theorem prefix_eq_of_fixed {n q : ℕ} (S T : State n q) (c : ℕ)
    (h : ∀ x : Fin n, x.val < c → (x ∈ S.val ↔ x ∈ T.val)) :
    S.prefixCount c = T.prefixCount c := by
  rw [prefix_card,prefix_card]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  by_cases hx : x.val < c
  · rw [h x hx]
  · simp [hx]

/-- Counts in a joined middle block are the actual local cardinality. -/
theorem blockCount_join {a b c u v z : ℕ}
    (S₀ : State a u) (S₁ : State b v) (S₂ : State c z) :
    (join S₀ (join S₁ S₂)).blockCount a b = v := by
  classical
  unfold blockCount
  calc
    _ = S₁.val.card := by
      apply Finset.card_bij (fun x hx => ⟨x.val-a,by
        have hh := (Finset.mem_filter.mp hx).2
        omega⟩)
      · intro x hx
        obtain ⟨hmem,hlo,hhi⟩ := Finset.mem_filter.mp hx
        have hx' : x = Fin.natAdd a (Fin.castAdd c (⟨x.val-a,by omega⟩ : Fin b)) := by
          apply Fin.ext
          simp only [Fin.val_natAdd,Fin.val_castAdd]
          omega
        rw [hx'] at hmem
        simpa only [join_mem_right,join_mem_left] using hmem
      · intro x hx y hy hxy
        obtain ⟨_,hx,_⟩ := Finset.mem_filter.mp hx
        obtain ⟨_,hy,_⟩ := Finset.mem_filter.mp hy
        have hv := congrArg Fin.val hxy
        apply Fin.ext
        dsimp only at hv
        omega
      · intro y hy
        refine ⟨Fin.natAdd a (Fin.castAdd c y),?_,?_⟩
        · simp only [Finset.mem_filter,join_mem_right,join_mem_left,
            Fin.val_natAdd,Fin.val_castAdd]
          exact ⟨hy,by omega,by have := y.isLt; omega⟩
        · apply Fin.ext
          simp
    _ = v := S₁.property
end State

/-- Every translated letter acts strictly inside the selected middle block. -/
theorem middleWord_index_bounds {b : ℕ} (a c : ℕ) (w : List (Letter b))
    (l : Letter (a+(b+c))) (hl : l ∈ middleWord a c w) :
    a ≤ l.index.val ∧ l.index.val + 1 < a+b := by
  obtain ⟨l₁,hl₁,rfl⟩ := List.mem_map.mp hl
  obtain ⟨l₀,_,rfl⟩ := List.mem_map.mp hl₁
  have hi := l₀.index.isLt
  simp only [Letter.inRight,Letter.inLeft,rightIndex,leftIndex]
  omega

/-- Positions to the left of the middle block are fixed by the whole word. -/
theorem word_middle_fixed_left {a b c q : ℕ} (w : List (Letter b))
    (S T : State (a+(b+c)) q)
    (h : wordMatrix q (middleWord a c w) S T ≠ 0) :
    ∀ x : Fin (a+(b+c)), x.val < a → (x ∈ S.val ↔ x ∈ T.val) :=
  word_fixed_prefix (middleWord a c w) a
    (fun l hl => (middleWord_index_bounds a c w l hl).1) S T h

 theorem word_middle_prefix_left {a b c q : ℕ} (w : List (Letter b))
    (S T : State (a+(b+c)) q)
    (h : wordMatrix q (middleWord a c w) S T ≠ 0) :
    S.prefixCount a = T.prefixCount a :=
  State.prefix_eq_of_fixed S T a (word_middle_fixed_left w S T h)

/-- No occupied track can return through the right boundary of the acted-on block. -/
theorem word_middle_prefix_right {a b c q : ℕ} (w : List (Letter b))
    (S T : State (a+(b+c)) q)
    (h : wordMatrix q (middleWord a c w) S T ≠ 0) :
    T.prefixCount (a+b) ≤ S.prefixCount (a+b) :=
  word_prefix_outside (middleWord a c w) (a+b)
    (fun l hl => by have hh := (middleWord_index_bounds a c w l hl).2; omega) S T h

/-- First assertion of Lemma 4.2, with no assumption on outside occupations. -/
theorem word_middle_block_count_le {a b c q : ℕ} (w : List (Letter b))
    (S T : State (a+(b+c)) q)
    (h : wordMatrix q (middleWord a c w) S T ≠ 0) :
    T.blockCount a b ≤ S.blockCount a b := by
  have hl := word_middle_prefix_left w S T h
  have hr := word_middle_prefix_right w S T h
  have hS := S.prefix_add_blockCount a b
  have hT := T.prefix_add_blockCount a b
  omega

/-- Both parts of restriction without boundary flow: arbitrary nonzero entries cannot
increase block occupancy, and every fixed three-part sector has the exact local entry. -/
theorem middleWord_restriction {a b c : ℕ} (w : List (Letter b)) :
    (∀ q (S T : State (a+(b+c)) q),
      wordMatrix q (middleWord a c w) S T ≠ 0 → T.blockCount a b ≤ S.blockCount a b) ∧
    (∀ u v z (S₀ T₀ : State a u) (S₁ T₁ : State b v) (S₂ T₂ : State c z),
      wordMatrix (u+(v+z)) (middleWord a c w)
        (State.join S₀ (State.join S₁ S₂)) (State.join T₀ (State.join T₁ T₂)) =
        (if S₀=T₀ then 1 else 0) * wordMatrix v w S₁ T₁ * (if S₂=T₂ then 1 else 0)) :=
  ⟨fun _ S T h => word_middle_block_count_le w S T h,
    fun _ _ _ S₀ T₀ S₁ T₁ S₂ T₂ => word_middle_entry w S₀ T₀ S₁ T₁ S₂ T₂⟩

end HiddenCircuits
