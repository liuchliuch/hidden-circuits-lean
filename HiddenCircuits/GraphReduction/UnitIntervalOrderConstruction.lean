import HiddenCircuits.GraphReduction.UnitIntervalOrdering

/-! Literal rational unit-coordinate construction from an umbrella order.
Only finite rational extrema and midpoint arithmetic occur in the executable
part. The ordering proof inhabits erased proof fields; it is not a runtime
oracle or coordinate certificate. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalOrder

def separator (A B : Finset ℚ) (hA : A.Nonempty) : ℚ :=
  if hB : B.Nonempty then (A.max' hA+B.min' hB)/2 else A.max' hA+1

lemma separator_spec (A B : Finset ℚ) (hA : A.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    (∀ a ∈ A, a < separator A B hA) ∧ ∀ b ∈ B, separator A B hA < b := by
  unfold separator
  split_ifs with hB
  · have hh := h (A.max' hA) (A.max'_mem hA) (B.min' hB) (B.min'_mem hB)
    constructor
    · intro a ha; have := A.le_max' a ha; linarith
    · intro b hb; have := B.min'_le b hb; linarith
  · constructor
    · intro a ha; have := A.le_max' a ha; linarith
    · intro b hb; exact (hB ⟨b,hb⟩).elim

def buildModel : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Umbrella G → StrictModel G := by
  intro n
  induction n with
  | zero =>
    intro G _ _
    refine { left := Fin.elim0, nonnegative := ?_, increasing := ?_, edge := ?_, nonedge := ?_ }
    all_goals intro i; exact Fin.elim0 i
  | succ n ih =>
    intro G _ hG
    let H := G.comap Fin.castSucc
    have hH : Umbrella H := by
      intro i j k hij hjk hik
      exact hG i.castSucc j.castSucc k.castSucc hij hjk hik
    let r := ih H hH
    let A : Finset ℚ := insert 0 (Finset.univ.image r.left ∪
      (Finset.univ.filter (fun i : Fin n => ¬G.Adj i.castSucc (Fin.last n))).image (fun i => r.left i+1))
    let B : Finset ℚ :=
      (Finset.univ.filter (fun i : Fin n => G.Adj i.castSucc (Fin.last n))).image (fun i => r.left i+1)
    have hA : A.Nonempty := ⟨0,by simp [A]⟩
    have hsep : ∀ a ∈ A, ∀ b ∈ B, a < b := by
      intro a ha b hb
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
      have hj : G.Adj j.castSucc (Fin.last n) := (Finset.mem_filter.mp hj).2
      simp only [A,Finset.mem_insert,Finset.mem_union,Finset.mem_image,Finset.mem_univ,
        true_and,Finset.mem_filter] at ha
      rcases ha with rfl | ⟨i,rfl⟩ | ⟨i,hi,rfl⟩
      · linarith [r.nonnegative j]
      · by_cases hij : i ≤ j
        · have := r.increasing.monotone hij; linarith
        · have hji : j < i := lt_of_not_ge hij
          have he : H.Adj j i := (hG j.castSucc i.castSucc (Fin.last n)
            hji (Fin.castSucc_lt_last i) hj).1
          exact r.edge j i hji he
      · have hij : i < j := by
          by_contra hn
          have hji : j ≤ i := le_of_not_gt hn
          rcases eq_or_lt_of_le hji with he | he
          · subst i; exact hi hj
          · exact hi ((hG j.castSucc i.castSucc (Fin.last n) he (Fin.castSucc_lt_last i) hj).2)
        have := r.increasing hij
        linarith
    let y := separator A B hA
    have hyA := (separator_spec A B hA hsep).1
    have hyB := (separator_spec A B hA hsep).2
    have hy0 : 0 < y := hyA 0 (by simp [A])
    have hyi : ∀ i, r.left i < y := fun i => hyA _ (by simp [A])
    have hye : ∀ i : Fin n, G.Adj i.castSucc (Fin.last n) → y < r.left i+1 := by
      intro i hi
      exact hyB _ (by simpa only [B,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and] using ⟨i,hi,rfl⟩)
    have hyn : ∀ i : Fin n, ¬G.Adj i.castSucc (Fin.last n) → r.left i+1 < y := by
      intro i hi
      exact hyA _ (by
        apply Finset.mem_insert_of_mem
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨i,by simp [hi],rfl⟩)
    refine { left := Fin.snoc r.left y, nonnegative := ?_, increasing := ?_, edge := ?_, nonedge := ?_ }
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hy0.le
      · simpa using r.nonnegative i
    · intro i j hij
      revert hij
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij
        exact False.elim (not_lt_of_ge (Fin.le_last j) hij)
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _; simpa using hyi i
        · intro hij; simpa using r.increasing hij
    · intro i j hij he
      revert hij he
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij; exact False.elim (not_lt_of_ge (Fin.le_last j) hij)
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _ he; simpa using hye i he
        · intro hij he; simpa using r.edge i j hij he
    · intro i j hij he
      revert hij he
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij; exact False.elim (not_lt_of_ge (Fin.le_last j) hij)
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _ he; simpa using hyn i he
        · intro hij he; simpa using r.nonedge i j hij he


end HiddenCircuits.GraphReduction.UnitIntervalOrder
