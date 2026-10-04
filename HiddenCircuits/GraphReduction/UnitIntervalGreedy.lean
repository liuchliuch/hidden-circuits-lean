import HiddenCircuits.GraphReduction.RealUnitIntervalGrid

/-! The endpoint-selection invariant behind an elementary polynomial recognizer.
Maximize adjacency to the selected prefix, then minimize closed degree. Starting
at a leftmost vertex, every positive-frontier choice is a true twin of a
leftmost remaining vertex. This lemma is not by itself a recognition endpoint. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalGreedy
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Reflexive adjacency makes true-twin comparison include the vertices themselves. -/
def ClosedAdj (G : SimpleGraph V) (v w : V) : Prop := v=w ∨ G.Adj v w

lemma closedAdj_iff (r : RealUnitInterval.Representation G) (v w : V) :
    ClosedAdj G v w ↔ r.left v ≤ r.left w+r.length ∧ r.left w ≤ r.left v+r.length := by
  by_cases he : v=w
  · subst w
    simp only [ClosedAdj,true_or]
    exact iff_of_true trivial ⟨by linarith [r.positive],by linarith [r.positive]⟩
  · simp only [ClosedAdj,he,false_or]
    rw [r.adjacency,and_iff_right he]
    exact RealUnitInterval.icc_overlap (by linarith [r.positive]) (by linarith [r.positive])

section
variable [DecidableEq V] [DecidableRel G.Adj]

instance closedAdj_decidable (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (ClosedAdj G) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _ ∨ G.Adj _ _))

def neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : Finset V :=
  S.filter (ClosedAdj G v)

def degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ := (neighbors G Finset.univ v).card

def score (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (neighbors G S v).card

lemma neighbors_mono_left (r : RealUnitInterval.Representation G) (S : Finset V)
    {x y : V} (hxy : r.left x ≤ r.left y) (hS : ∀ v ∈ S, r.left v ≤ r.left x) :
    neighbors G S y ⊆ neighbors G S x := by
  intro v hv
  obtain ⟨hv,hvy⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_filter.mpr ⟨hv,?_⟩
  rw [closedAdj_iff r] at hvy ⊢
  have hh := hS v hv
  constructor <;> linarith [r.positive]

/-- The exact selection rule needs only integer adjacency counts and degrees.
No coordinate or ordering certificate is part of the rule. -/
def Preferred (G : SimpleGraph V) [DecidableRel G.Adj] (S R : Finset V) (y : V) : Prop :=
  y ∈ R ∧ ∀ x ∈ R,
    score G S x ≤ score G S y ∧
      (score G S x = score G S y → degree G y ≤ degree G x)

/-- Positive-frontier greedy choices can differ from the current leftmost
remaining vertex only by true twins. -/
theorem preferred_twin (r : RealUnitInterval.Representation G) (S R : Finset V)
    (hcover : ∀ v, v ∈ S ∨ v ∈ R) {x y : V} (hx : x ∈ R)
    (hprefix : ∀ v ∈ S, ∀ w ∈ R, r.left v ≤ r.left w)
    (hxmin : ∀ w ∈ R, r.left x ≤ r.left w)
    (hy : Preferred G S R y) (hpositive : 0 < score G S x) :
    neighbors G Finset.univ x = neighbors G Finset.univ y := by
  have hxy := hxmin y hy.1
  have hsub := neighbors_mono_left r S hxy (fun v hv => hprefix v hv x hx)
  have hscore := (hy.2 x hx).1
  have heq : neighbors G S y = neighbors G S x :=
    Finset.eq_of_subset_of_card_le hsub hscore
  have heqscore : score G S x = score G S y := by unfold score; rw [heq]
  have hdegree := (hy.2 x hx).2 heqscore
  have hnonempty : (neighbors G S x).Nonempty := Finset.card_pos.mp hpositive
  obtain ⟨z,hz⟩ := hnonempty
  have hzx := (Finset.mem_filter.mp hz).2
  have hzS := (Finset.mem_filter.mp hz).1
  have hzy : ClosedAdj G y z := (Finset.mem_filter.mp (show z ∈ neighbors G S y by rw [heq]; exact hz)).2
  have hzleft := hprefix z hzS x hx
  apply Finset.eq_of_subset_of_card_le _ hdegree
  intro w hw
  obtain ⟨_,hwx⟩ := Finset.mem_filter.mp hw
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ w,?_⟩
  rcases hcover w with hwS | hwR
  · have hw' : w ∈ neighbors G S x := Finset.mem_filter.mpr ⟨hwS,hwx⟩
    rw [←heq] at hw'
    exact (Finset.mem_filter.mp hw').2
  · rw [closedAdj_iff r] at hwx hzy ⊢
    have hxw := hxmin w hwR
    rcases le_total (r.left w) (r.left y) with hwy | hyw
    · constructor <;> linarith [r.positive]
    · constructor <;> linarith [r.positive]

end
end HiddenCircuits.GraphReduction.UnitIntervalGreedy

namespace HiddenCircuits.GraphReduction.UnitIntervalGreedy
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma closedAdj_comm (x y : V) : ClosedAdj G x y ↔ ClosedAdj G y x := by
  simp only [ClosedAdj,eq_comm,G.adj_comm]

lemma twins_iff {x y : V} (h : neighbors G Finset.univ x = neighbors G Finset.univ y) (z : V) :
    ClosedAdj G x z ↔ ClosedAdj G y z := by
  have := congrArg (fun s : Finset V => z ∈ s) h
  simpa only [neighbors,Finset.mem_filter,Finset.mem_univ,true_and] using iff_of_eq this

lemma twins_swap_left {x y : V} (h : neighbors G Finset.univ x = neighbors G Finset.univ y)
    (v w : V) : ClosedAdj G (Equiv.swap x y v) w ↔ ClosedAdj G v w := by
  by_cases hvx : v=x
  · subst v; simpa using (twins_iff h w).symm
  · by_cases hvy : v=y
    · subst v; simpa using twins_iff h w
    · rw [Equiv.swap_apply_of_ne_of_ne hvx hvy]

lemma twins_swap_adj {x y : V} (h : neighbors G Finset.univ x = neighbors G Finset.univ y)
    (v w : V) : G.Adj (Equiv.swap x y v) (Equiv.swap x y w) ↔ G.Adj v w := by
  have hc : ClosedAdj G (Equiv.swap x y v) (Equiv.swap x y w) ↔ ClosedAdj G v w := by
    rw [twins_swap_left h,closedAdj_comm,twins_swap_left h,closedAdj_comm]
  by_cases hvw : v=w
  · subst w; simp
  · have hs : Equiv.swap x y v ≠ Equiv.swap x y w := (Equiv.swap x y).injective.ne hvw
    simpa only [ClosedAdj,hvw,hs,false_or] using hc

/-- A true-twin exchange alters only the labels on two intervals, preserving
all edges and all closed-boundary/coincidence conventions. -/
def swapRepresentation (r : RealUnitInterval.Representation G) {x y : V}
    (h : neighbors G Finset.univ x = neighbors G Finset.univ y) : RealUnitInterval.Representation G where
  length := r.length
  positive := r.positive
  left v := r.left (Equiv.swap x y v)
  adjacency v w := by
    rw [←twins_swap_adj h v w,r.adjacency]
    simp only [ne_eq,(Equiv.swap x y).injective.eq_iff]

end HiddenCircuits.GraphReduction.UnitIntervalGreedy
