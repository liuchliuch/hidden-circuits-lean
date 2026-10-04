import HiddenCircuits.GraphReduction.PermutationRankCompression

/-! A finite right-endpoint order with suffix neighborhoods gives explicit,
nonnegative integer interval endpoints by two comparison-count scans. -/
namespace HiddenCircuits.GraphReduction.Interval
variable {V : Type*}

/-- A literal closed rational interval representation, allowing singleton intervals. -/
structure Representation (G : SimpleGraph V) where
  left : V → ℚ
  right : V → ℚ
  ordered : ∀ v, left v ≤ right v
  adjacency : ∀ x y, G.Adj x y ↔ x ≠ y ∧
    (Set.Icc (left x) (right x) ∩ Set.Icc (left y) (right y)).Nonempty

/-- Natural endpoints are an especially simple exact integer representation. -/
structure NatRepresentation (G : SimpleGraph V) where
  left : V → ℕ
  right : V → ℕ
  ordered : ∀ v, left v ≤ right v
  adjacency : ∀ x y, G.Adj x y ↔ x ≠ y ∧ left x ≤ right y ∧ left y ≤ right x

def NatRepresentation.toRational {G : SimpleGraph V} (r : NatRepresentation G) :
    Representation G where
  left v := r.left v
  right v := r.right v
  ordered v := by exact_mod_cast r.ordered v
  adjacency x y := by
    rw [r.adjacency]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨hxy,hyx⟩
      refine ⟨max (r.left x : ℚ) (r.left y : ℚ), ?_⟩
      constructor <;> constructor
      · exact le_max_left _ _
      · exact max_le (by exact_mod_cast r.ordered x) (by exact_mod_cast hyx)
      · exact le_max_right _ _
      · exact max_le (by exact_mod_cast hxy) (by exact_mod_cast r.ordered y)
    · rintro ⟨z,⟨hxl,hxr⟩,⟨hyl,hyr⟩⟩
      exact ⟨by exact_mod_cast hxl.trans hyr, by exact_mod_cast hyl.trans hxr⟩

/-- Earlier neighbors of each vertex are a suffix of the right-endpoint order. -/
def SuffixOrder (G : SimpleGraph V) (f : V → ℕ) : Prop :=
  ∀ x y z, f x ≤ f y → f y < f z → G.Adj x z → G.Adj y z

section Finite
variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def rightCount (f : V → ℕ) (v : V) : ℕ :=
  (Finset.univ.filter (fun x => f x < f v)).card

def leftCount (f : V → ℕ) (v : V) : ℕ :=
  (Finset.univ.filter (fun x => f x < f v ∧ ¬G.Adj x v)).card

lemma leftCount_le_rightCount (f : V → ℕ) (v : V) : leftCount (G:=G) f v ≤ rightCount f v := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
  exact hx.1

lemma leftCount_le_iff {f : V → ℕ} (hf : Function.Injective f) (hs : SuffixOrder G f)
    {x y : V} (hxy : f x < f y) : leftCount (G:=G) f y ≤ rightCount f x ↔ G.Adj x y := by
  constructor
  · intro hc
    by_contra hn
    have hsub : (Finset.univ.filter (fun z => f z < f x)) ⊂
        (Finset.univ.filter (fun z => f z < f y ∧ ¬G.Adj z y)) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro z hz
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
        refine ⟨hz.trans hxy, ?_⟩
        intro hzy
        exact hn (hs z x y (Nat.le_of_lt hz) hxy hzy)
      · intro he
        have hm : x ∈ Finset.univ.filter (fun z => f z < f y ∧ ¬G.Adj z y) := by simp [hxy,hn]
        rw [←he] at hm
        simpa using hm
    exact (Nat.not_lt_of_ge hc) (Finset.card_lt_card hsub)
  · intro ha
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    by_contra hn
    exact hz.2 (hs x z y (Nat.le_of_not_gt hn) hz.1 ha)

lemma rightCount_lt {f : V → ℕ} (hf : Function.Injective f) {x y : V}
    (hxy : f x < f y) : rightCount f x < rightCount f y := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact hz.trans hxy
  · intro he
    have hm : x ∈ Finset.univ.filter (fun z => f z < f y) := by simp [hxy]
    rw [←he] at hm
    simpa using hm

/-- Both vectors are executable finite counts, including when the vertex set is empty. -/
def ofSuffixOrder (f : V ↪ ℕ) (hs : SuffixOrder G f) : NatRepresentation G where
  left := leftCount f
  right := rightCount f
  ordered := leftCount_le_rightCount f
  adjacency x y := by
    change G.Adj x y ↔ x ≠ y ∧ leftCount (G:=G) f x ≤ rightCount f y ∧ leftCount (G:=G) f y ≤ rightCount f x
    by_cases he : x=y
    · subst y
      simp
    have hne : f x ≠ f y := fun h => he (f.injective h)
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · have hl := (leftCount_le_rightCount (G:=G) f x).trans (Nat.le_of_lt (rightCount_lt f.injective hxy))
      simp only [ne_eq,he,not_false_eq_true,true_and,hl]
      exact (leftCount_le_iff f.injective hs hxy).symm
    · have hl := (leftCount_le_rightCount (G:=G) f y).trans (Nat.le_of_lt (rightCount_lt f.injective hyx))
      simp only [ne_eq,he,not_false_eq_true,true_and,hl,and_true]
      rw [G.adj_comm]
      exact (leftCount_le_iff f.injective hs hyx).symm

lemma ofSuffixOrder_bounds (f : V ↪ ℕ) (hs : SuffixOrder G f) (v : V) :
    (ofSuffixOrder (G:=G) f hs).left v ≤ (ofSuffixOrder (G:=G) f hs).right v ∧
      (ofSuffixOrder (G:=G) f hs).right v < Fintype.card V := by
  refine ⟨leftCount_le_rightCount f v, ?_⟩
  change (Finset.univ.filter (fun x => f x < f v)).card < _
  rw [←Finset.card_univ]
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, by
    intro he
    have hv : v ∈ Finset.univ.filter (fun x => f x < f v) := by rw [he]; simp
    simpa using hv⟩

end Finite
end HiddenCircuits.GraphReduction.Interval
