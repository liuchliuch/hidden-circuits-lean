import HiddenCircuits.IntegralTransfers

namespace HiddenCircuits
open scoped BigOperators

namespace State
/-- Number of occupied tracks strictly before a cut. Cuts outside the track range are harmless. -/
def prefixCount {n q : ℕ} (S : State n q) (c : ℕ) : ℕ :=
  ∑ x ∈ S.val, if x.val < c then 1 else 0

theorem prefix_card {n q : ℕ} (S : State n q) (c : ℕ) :
    S.prefixCount c = (S.val.filter (fun x => x.val<c)).card := by
  simp only [prefixCount, Finset.sum_boole, Nat.cast_id]

theorem prefix_tracks {n q : ℕ} (S : State n q) (c : ℕ) :
    S.prefixCount c = ∑ j : Fin q, if (S.track j).val<c then 1 else 0 := by
  unfold prefixCount
  rw [← S.image_track]
  exact Finset.sum_image (fun _ _ _ _ h => S.track.injective h)

theorem prefix_complement_add {n q : ℕ} (S : State n q) (c : ℕ) :
    S.prefixCount c + S.complement.prefixCount c =
      ∑ x : Fin n, if x.val<c then 1 else 0 := by
  exact Finset.sum_add_sum_compl S.val _
end State

/-- Every nonzero permanent contributes an actual bijection using nonzero cut entries. -/
theorem compound_nonzero_bijection {n q : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (S T : State n q) (h : compound M S T ≠ 0) :
    ∃ σ : Equiv.Perm (Fin q), ∀ j, M (S.track (σ j)) (T.track j) ≠ 0 := by
  obtain ⟨σ,_,hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨σ, fun j => (Finset.prod_ne_zero_iff.mp hσ) j (Finset.mem_univ j)⟩

/-- Support relation in the direction used for row-vector transfers. -/
def PrefixFlow {n q : ℕ} (M : Matrix (State n q) (State n q) ℚ) : Prop :=
  ∀ S T, M S T ≠ 0 → ∀ c, T.prefixCount c ≤ S.prefixCount c

namespace PrefixFlow
variable {n q : ℕ}
 theorem one : PrefixFlow (1 : Matrix (State n q) (State n q) ℚ) := by
  intro S T h c
  by_cases he:S=T
  · subst T; rfl
  · exact False.elim (h (by simp [Matrix.one_apply,he]))
 theorem mul {A B : Matrix (State n q) (State n q) ℚ}
    (hA : PrefixFlow A) (hB : PrefixFlow B) : PrefixFlow (A*B) := by
  intro S T h c
  rw [Matrix.mul_apply] at h
  obtain ⟨K,_,hK⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (hB K T (fun hz => hK (by rw [hz,mul_zero])) c).trans
    (hA S K (fun hz => hK (by rw [hz,zero_mul])) c)
 theorem neg {A : Matrix (State n q) (State n q) ℚ} (hA : PrefixFlow A) : PrefixFlow (-A) := by
  intro S T h
  exact hA S T (fun hz => h (by simp [hz]))
 theorem sub {A B : Matrix (State n q) (State n q) ℚ}
    (hA : PrefixFlow A) (hB : PrefixFlow B) : PrefixFlow (A-B) := by
  intro S T h
  by_cases ha:A S T=0
  · exact hB S T (fun hb => h (by simp [ha,hb]))
  · exact hA S T ha
 theorem pow {A : Matrix (State n q) (State n q) ℚ} (hA : PrefixFlow A) :
    ∀ k, PrefixFlow (A^k)
  | 0 => by simpa using one
  | k+1 => by rw [pow_succ]; exact (pow hA k).mul hA
 theorem sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (State n q) (State n q) ℚ)
    (hA : ∀ i ∈ s, PrefixFlow (A i)) : PrefixFlow (∑ i ∈ s, A i) := by
  intro S T h
  rw [Matrix.sum_apply] at h
  obtain ⟨i,hi,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact hA i hi S T hv
end PrefixFlow

theorem upper_prefix_flow (n q : ℕ) : PrefixFlow (compound (q:=q) (upper n)) := by
  intro S T h c
  obtain ⟨σ,hσ⟩ := compound_nonzero_bijection (upper n) S T h
  have hs : ∀ j, (S.track (σ j)).val ≤ (T.track j).val := by
    intro j
    have hh := hσ j
    simpa [upper] using hh
  rw [State.prefix_tracks,State.prefix_tracks]
  have ht := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
    show (if (T.track j).val<c then 1 else 0) ≤ (if (S.track (σ j)).val<c then 1 else 0) by
      have hj := hs j
      split_ifs <;> omega)
  rw [Equiv.sum_comp σ (fun j => if (S.track j).val<c then 1 else 0)] at ht
  exact ht

theorem upperInverse_prefix_flow (n q : ℕ) : PrefixFlow (upperInverse n q) := by
  unfold upperInverse inverseSeries
  apply PrefixFlow.sum
  intro a _
  exact ((upper_prefix_flow n q).sub PrefixFlow.one).neg.pow a

/-- Deleted diagonal edges introduce no backward prefixCount flow, even before normalization. -/
theorem deletedCut_prefix_flow {n q : ℕ} (i : Fin (n-1)) :
    PrefixFlow (compound (q:=q) (deletedCut i)) := by
  intro S T h c
  obtain ⟨σ,hσ⟩ := compound_nonzero_bijection (deletedCut i) S T h
  have hs : ∀ j, (S.track (σ j)).val ≤ (T.track j).val := by
    intro j
    have hh := hσ j
    unfold deletedCut upper at hh
    split_ifs at hh <;> simp_all
  rw [State.prefix_tracks,State.prefix_tracks]
  have ht := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
    show (if (T.track j).val<c then 1 else 0) ≤ (if (S.track (σ j)).val<c then 1 else 0) by
      have hj := hs j
      split_ifs <;> omega)
  rw [Equiv.sum_comp σ (fun j => if (S.track j).val<c then 1 else 0)] at ht
  exact ht

theorem drop_prefix_flow (n q : ℕ) (i : Fin (n-1)) : PrefixFlow (drop n q i) :=
  deletedCut_prefix_flow i |>.mul (upperInverse_prefix_flow n q)

/-- Complementing both states and reversing input/output preserves one-way prefixCount flow. -/
theorem dualDrop_prefix_flow (n q : ℕ) (i : Fin (n-1)) : PrefixFlow (dualDrop n q i) := by
  intro S T h c
  have hc := drop_prefix_flow n (n-q) i T.complement S.complement h c
  have hS := S.prefix_complement_add c
  have hT := T.prefix_complement_add c
  omega


/-- The single added edge can cross backward only at its own internal track boundary. -/
theorem addedCut_pair {n : ℕ} (i : Fin (n-1)) (a b : Fin n)
    (h : addedCut i a b ≠ 0) :
    a.val ≤ b.val ∨ (a.val=i.val+1 ∧ b.val=i.val) := by
  unfold addedCut upper at h
  split_ifs at h with he hab
  · exact Or.inr he
  · exact Or.inl hab
  · simp at h

theorem addedCut_prefix_bound {n q : ℕ} (i : Fin (n-1)) (S T : State n q)
    (h : compound (addedCut i) S T ≠ 0) (c : ℕ) :
    T.prefixCount c ≤ S.prefixCount c + if c=i.val+1 then 1 else 0 := by
  obtain ⟨σ,hσ⟩ := compound_nonzero_bijection (addedCut i) S T h
  have hp := fun j => addedCut_pair i (S.track (σ j)) (T.track j) (hσ j)
  rw [State.prefix_tracks,State.prefix_tracks]
  by_cases hc:c=i.val+1
  · rw [if_pos hc]
    have hpoint : ∀ j,
        (if (T.track j).val<c then 1 else 0) ≤
          (if (S.track (σ j)).val<c then 1 else 0) +
          (if (S.track (σ j)).val=i.val+1 then 1 else 0) := by
      intro j
      have hh := hp j
      split_ifs <;> omega
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hpoint j)
    rw [Finset.sum_add_distrib,
      Equiv.sum_comp σ (fun j => if (S.track j).val<c then 1 else 0)] at hs
    have hone : (∑ j : Fin q, if (S.track (σ j)).val=i.val+1 then 1 else 0) ≤ 1 := by
      simp only [Finset.sum_boole, Nat.cast_id]
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
      exact σ.injective (S.track.injective (Fin.ext (ha.trans hb.symm)))
    omega
  · rw [if_neg hc,add_zero]
    have hpoint : ∀ j,
        (if (T.track j).val<c then 1 else 0) ≤
          (if (S.track (σ j)).val<c then 1 else 0) := by
      intro j
      have hh := hp j
      split_ifs <;> omega
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hpoint j)
    rw [Equiv.sum_comp σ (fun j => if (S.track j).val<c then 1 else 0)] at hs
    exact hs

theorem rise_prefix_bound (n q : ℕ) (i : Fin (n-1)) (S T : State n q)
    (h : rise n q i S T ≠ 0) (c : ℕ) :
    T.prefixCount c ≤ S.prefixCount c + if c=i.val+1 then 1 else 0 := by
  change (compound (q:=q) (addedCut i) * upperInverse n q) S T ≠ 0 at h
  rw [Matrix.mul_apply] at h
  obtain ⟨K,_,hK⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (upperInverse_prefix_flow n q K T (fun hz => hK (by rw [hz,mul_zero])) c).trans
    (addedCut_prefix_bound i S K (fun hz => hK (by rw [hz,zero_mul])) c)

theorem dualRise_prefix_bound (n q : ℕ) (i : Fin (n-1)) (S T : State n q)
    (h : dualRise n q i S T ≠ 0) (c : ℕ) :
    T.prefixCount c ≤ S.prefixCount c + if c=i.val+1 then 1 else 0 := by
  have hh := rise_prefix_bound n (n-q) i T.complement S.complement h c
  have hS := S.prefix_complement_add c
  have hT := T.prefix_complement_add c
  omega

/-- Every elementary letter is one-way at every cut outside its two acted-on tracks. -/
theorem letter_prefix_outside {n q : ℕ} (l : Letter n) (S T : State n q)
    (h : l.matrix q S T ≠ 0) (c : ℕ) (hc : c ≠ l.index.val+1) :
    T.prefixCount c ≤ S.prefixCount c := by
  cases l with
  | mk kind i =>
    cases kind with
    | R => simpa only [if_neg hc,add_zero] using rise_prefix_bound n q i S T h c
    | D => exact drop_prefix_flow n q i S T h c
    | B => simpa only [if_neg hc,add_zero] using dualRise_prefix_bound n q i S T h c
    | E => exact dualDrop_prefix_flow n q i S T h c

/-- A whole listed word cannot return across any boundary untouched by its letter indices. -/
theorem word_prefix_outside {n q : ℕ} (w : List (Letter n)) (c : ℕ)
    (hc : ∀ l ∈ w, c ≠ l.index.val+1) :
    ∀ S T, wordMatrix q w S T ≠ 0 → T.prefixCount c ≤ S.prefixCount c := by
  induction w with
  | nil => exact fun S T h => PrefixFlow.one S T h c
  | cons l w ih =>
    intro S T h
    rw [wordMatrix_cons,Matrix.mul_apply] at h
    obtain ⟨K,_,hK⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have htail := ih (fun a ha => hc a (by simp [ha])) K T
      (fun hz => hK (by rw [hz,mul_zero]))
    exact htail.trans (letter_prefix_outside l S K
      (fun hz => hK (by rw [hz,zero_mul])) c (hc l (by simp)))

end HiddenCircuits
