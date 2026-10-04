import HiddenCircuits.GraphReduction.RealUnitIntervalGrid
import HiddenCircuits.Approximation.RealOrderedIntervals

/-! The umbrella ordering characterization, with labeled coincident intervals.
All finite ordered graphs, including the empty graph, are covered. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalOrder

/-- Every edge covers a clique in the supplied order. -/
def Umbrella {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j k, i < j → j < k → G.Adj i k → G.Adj i j ∧ G.Adj j k

/-- A strictly separated rational model is convenient for inductive extension:
edges have distance strictly below one and nonedges strictly above one. -/
structure StrictModel {n : ℕ} (G : SimpleGraph (Fin n)) where
  left : Fin n → ℚ
  nonnegative : ∀ i, 0 ≤ left i
  increasing : StrictMono left
  edge : ∀ i j, i < j → G.Adj i j → left j < left i + 1
  nonedge : ∀ i j, i < j → ¬G.Adj i j → left i + 1 < left j

private lemma separate (A B : Finset ℚ) (hA : A.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ y : ℚ, (∀ a ∈ A, a < y) ∧ ∀ b ∈ B, y < b := by
  by_cases hB : B.Nonempty
  · obtain ⟨y,hy₁,hy₂⟩ := exists_between (h (A.max' hA) (A.max'_mem hA)
      (B.min' hB) (B.min'_mem hB))
    exact ⟨y,fun a ha => (A.le_max' a ha).trans_lt hy₁,
      fun b hb => hy₂.trans_le (B.min'_le b hb)⟩
  · refine ⟨A.max' hA+1,fun a ha => ?_,?_⟩
    · have := A.le_max' a ha; linarith
    · intro b hb; exact (hB ⟨b,hb⟩).elim

/-- An umbrella order itself suffices to construct a rational unit model.
No interval representation is assumed. -/
theorem exists_strictModel : ∀ n (G : SimpleGraph (Fin n)), Umbrella G → Nonempty (StrictModel G) := by
  classical
  intro n
  induction n with
  | zero =>
    intro G _
    refine ⟨{ left := Fin.elim0, nonnegative := ?_, increasing := ?_, edge := ?_, nonedge := ?_ }⟩
    all_goals intro i; exact Fin.elim0 i
  | succ n ih =>
    intro G hG
    let H := G.comap Fin.castSucc
    have hH : Umbrella H := by
      intro i j k hij hjk hik
      exact hG i.castSucc j.castSucc k.castSucc hij hjk hik
    obtain ⟨r⟩ := ih H hH
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
    obtain ⟨y,hyA,hyB⟩ := separate A B hA hsep
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
    refine ⟨{ left := Fin.snoc r.left y, nonnegative := ?_, increasing := ?_, edge := ?_, nonedge := ?_ }⟩
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

/-- Strict models are literal closed rational interval representations. -/
def StrictModel.representation {n : ℕ} {G : SimpleGraph (Fin n)} (r : StrictModel G) :
    UnitInterval.Representation G where
  length := 1
  positive := by norm_num
  left := r.left
  adjacency i j := by
    rw [UnitInterval.icc_overlap (by linarith) (by linarith)]
    by_cases he : i=j
    · subst j; simp
    rcases lt_or_gt_of_ne he with hij | hji
    · have hm := r.increasing hij
      constructor
      · intro ha
        exact ⟨he,by linarith,(r.edge i j hij ha).le⟩
      · rintro ⟨_,_,ha⟩
        by_contra hn
        exact (not_lt_of_ge ha) (r.nonedge i j hij hn)
    · have hm := r.increasing hji
      constructor
      · intro ha
        exact ⟨he,(r.edge j i hji ha.symm).le,by linarith⟩
      · rintro ⟨_,ha,_⟩
        by_contra hn
        exact (not_lt_of_ge ha) (r.nonedge j i hji (fun h => hn h.symm))

end HiddenCircuits.GraphReduction.UnitIntervalOrder

namespace HiddenCircuits.GraphReduction.UnitIntervalOrder

lemma umbrella_of_monotone_endpoints {n : ℕ} {G : SimpleGraph (Fin n)}
    (l r : Fin n → ℝ) (hl : Monotone l) (hr : Monotone r)
    (hord : ∀ i, l i ≤ r i)
    (hadj : ∀ i j, G.Adj i j ↔ i ≠ j ∧ l i ≤ r j ∧ l j ≤ r i) : Umbrella G := by
  intro i j k hij hjk hik
  obtain ⟨_,_,hki⟩ := (hadj i k).mp hik
  constructor
  · exact (hadj i j).mpr ⟨ne_of_lt hij,(hl hij.le).trans (hord j),(hl hjk.le).trans hki⟩
  · exact (hadj j k).mpr ⟨ne_of_lt hjk,(hl hjk.le).trans (hord k),hki.trans (hr hij.le)⟩

/-- A graph order is an actual bijection of labeled vertices. -/
structure Ordering {V : Type*} [Fintype V] (G : SimpleGraph V) where
  vertices : Fin (Fintype.card V) ≃ V
  umbrella : Umbrella (G.comap vertices)

noncomputable def Ordering.rationalRepresentation {V : Type*} [Fintype V]
    {G : SimpleGraph V} (o : Ordering G) : UnitInterval.Representation G := by
  let r := (exists_strictModel _ (G.comap o.vertices) o.umbrella).some.representation
  refine { length := r.length, positive := r.positive, left := fun v => r.left (o.vertices.symm v), adjacency := ?_ }
  intro v w
  simpa only [SimpleGraph.comap_adj,Equiv.apply_symm_apply,ne_eq,o.vertices.symm.injective.eq_iff]
    using r.adjacency (o.vertices.symm v) (o.vertices.symm w)

/-- Every real equal-length representation gives an umbrella order by sorting
its left endpoints. Ties only order labels and do not perturb intervals. -/
noncomputable def _root_.HiddenCircuits.GraphReduction.RealUnitInterval.Representation.umbrellaOrdering
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (r : RealUnitInterval.Representation G) : Ordering G where
  vertices := Approximation.RealOrderedIntervals.coordinateOrder r.left
  umbrella := by
    let e := Approximation.RealOrderedIntervals.coordinateOrder r.left
    apply umbrella_of_monotone_endpoints (fun i => r.left (e i)) (fun i => r.left (e i)+r.length)
    · exact Approximation.RealOrderedIntervals.coordinateOrder_mono _
    · intro i j hij
      have := Approximation.RealOrderedIntervals.coordinateOrder_mono r.left hij
      linarith
    · intro i; linarith [r.positive]
    · intro i j
      change G.Adj (e i) (e j) ↔ _
      rw [r.adjacency,RealUnitInterval.icc_overlap (by linarith [r.positive]) (by linarith [r.positive])]
      simp only [ne_eq,e.injective.eq_iff]

theorem realUnitInterval_iff_ordering {V : Type*} [Fintype V] {G : SimpleGraph V} :
    RealUnitInterval.UnitIntervalGraph G ↔ Nonempty (Ordering G) := by
  constructor
  · rintro ⟨r⟩; exact ⟨r.umbrellaOrdering⟩
  · rintro ⟨o⟩; exact ⟨o.rationalRepresentation.toReal⟩

end HiddenCircuits.GraphReduction.UnitIntervalOrder
