import HiddenCircuits.GraphReduction.MonotoneDiagram

/-! Exhaustive verification that the Section 9 integer endpoint ranks represent
exactly the intended original cuts and probe edges. -/
namespace HiddenCircuits.GraphReduction

theorem fullMonotoneDiagram_adj {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ)
    (x y : MonotoneVertex (2*p) h s) :
    (fullMonotoneDiagram pairs s).graph.Adj x y ↔
      (digitRank (upperPosition pairs x)<digitRank (upperPosition pairs y) ∧
        digitRank (lowerPosition pairs y)<digitRank (lowerPosition pairs x)) ∨
      (digitRank (upperPosition pairs y)<digitRank (upperPosition pairs x) ∧
        digitRank (lowerPosition pairs x)<digitRank (lowerPosition pairs y)) := Iff.rfl

section Adjacencies
variable {p h s : ℕ} (pairs : Fin h → CutPair p)

theorem even_even_not_adj (j k : Fin (h+1)) (u v : Fin (2*p)) :
    ¬(fullMonotoneDiagram pairs s).graph.Adj (.inl (.inl (j,u))) (.inl (.inl (k,v))) := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent]
  rw [crossing_equal_blocks]
  rintro ⟨hj,hc⟩
  subst k
  simp only [upperBlock_even,lowerBlock_even,Nat.add_lt_add_iff_left,
    InterleaveMode.evenOffset_lt_iff] at hc
  omega

theorem odd_odd_not_adj (r t : Fin h) (u v : Fin (2*p)) :
    ¬(fullMonotoneDiagram pairs s).graph.Adj (.inr (.inl (r,u))) (.inr (.inl (t,v))) := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent,
    upperModeAt_castSucc,lowerModeAt_succ]
  rw [crossing_shifted_blocks]
  rintro ⟨hr,hc⟩
  subst t
  simp only [upperBlock_odd,lowerBlock_odd,Nat.add_lt_add_iff_left,
    InterleaveMode.oddOffset_lt_iff] at hc
  omega

theorem Q_Q_not_adj (r t : Fin h) (a b : Fin s) :
    ¬(fullMonotoneDiagram pairs s).graph.Adj (.inl (.inr (r,a))) (.inl (.inr (t,b))) := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent]
  rw [crossing_shifted_blocks]
  simp only [upperBlock_Q,lowerBlock_Q]
  omega

theorem P_P_not_adj (r t : Fin h) (a b : Fin s) :
    ¬(fullMonotoneDiagram pairs s).graph.Adj (.inr (.inr (r,a))) (.inr (.inr (t,b))) := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent]
  rw [crossing_shifted_blocks]
  simp only [upperBlock_P,lowerBlock_P]
  omega

theorem even_Q_not_adj (j : Fin (h+1)) (u : Fin (2*p)) (r : Fin h) (a : Fin s) :
    ¬(fullMonotoneDiagram pairs s).graph.Adj (.inl (.inl (j,u))) (.inl (.inr (r,a))) := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent]
  rw [crossing_neighbor_blocks]
  simp only [upperBlock_even,lowerBlock_even,upperBlock_Q,lowerBlock_Q]
  have he := (upperModeAt pairs j).evenOffset_lt u
  have ha := a.isLt
  omega

theorem odd_P_not_adj (r : Fin h) (u : Fin (2*p)) (t : Fin h) (a : Fin s) :
    ¬(fullMonotoneDiagram pairs s).graph.Adj (.inr (.inl (r,u))) (.inr (.inr (t,a))) := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent,
    upperModeAt_castSucc,lowerModeAt_succ]
  rw [crossing_shifted_blocks]
  simp only [upperBlock_odd,lowerBlock_odd,upperBlock_P,lowerBlock_P]
  have hu := (pairs r).upperMode.oddOffset_lt u
  have hl := (pairs r).lowerMode.oddOffset_lt u
  omega

/-- Every original first cut is M and every original second cut is its prescribed complement. -/
theorem even_odd_adj (j : Fin (h+1)) (u : Fin (2*p)) (r : Fin h) (v : Fin (2*p)) :
    (fullMonotoneDiagram pairs s).graph.Adj (.inl (.inl (j,u))) (.inr (.inl (r,v))) ↔
      queryRelation pairs (j,u) (r,v) := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent,
    upperModeAt_castSucc,lowerModeAt_succ]
  rw [crossing_neighbor_blocks]
  simp only [upperBlock_even,lowerBlock_even,upperBlock_odd,lowerBlock_odd,
    Nat.add_lt_add_iff_left,queryRelation]
  apply or_congr
  · apply and_congr_right
    intro hj
    rw [upperModeAt_eq pairs j r hj]
    exact (pairs r).upper_interleave_cut u v
  · apply and_congr_right
    intro hj
    rw [lowerModeAt_eq pairs j r hj]
    exact (pairs r).lower_interleave_cut v u

/-- P_r is adjacent to exactly the following even layer. -/
theorem even_P_adj (j : Fin (h+1)) (u : Fin (2*p)) (r : Fin h) (a : Fin s) :
    (fullMonotoneDiagram pairs s).graph.Adj (.inl (.inl (j,u))) (.inr (.inr (r,a))) ↔
      j.val=r.val+1 := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent]
  rw [crossing_neighbor_blocks]
  simp only [upperBlock_even,lowerBlock_even,upperBlock_P,lowerBlock_P]
  have hu := (upperModeAt pairs j).evenOffset_lt u
  have hl := (lowerModeAt pairs j).evenOffset_lt u
  omega

/-- Q_r is adjacent to exactly its odd layer. -/
theorem Q_odd_adj (r : Fin h) (a : Fin s) (t : Fin h) (v : Fin (2*p)) :
    (fullMonotoneDiagram pairs s).graph.Adj (.inl (.inr (r,a))) (.inr (.inl (t,v))) ↔ r=t := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent,
    upperModeAt_castSucc,lowerModeAt_succ]
  rw [crossing_shifted_blocks]
  simp only [upperBlock_Q,lowerBlock_Q,upperBlock_odd,lowerBlock_odd]
  have ht := (pairs t).upperMode.oddOffset_lt v
  have ha := a.isLt
  constructor
  · exact And.left
  · intro he
    exact ⟨he,Or.inr ⟨by omega,by omega⟩⟩

/-- Probe copies cross exactly inside their own designated pair. -/
theorem Q_P_adj (r t : Fin h) (a b : Fin s) :
    (fullMonotoneDiagram pairs s).graph.Adj (.inl (.inr (r,a))) (.inr (.inr (t,b))) ↔ r=t := by
  simp only [fullMonotoneDiagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,endpointContent]
  rw [crossing_shifted_blocks]
  simp only [upperBlock_Q,lowerBlock_Q,upperBlock_P,lowerBlock_P]
  have ha := a.isLt
  have hb := b.isLt
  constructor
  · exact And.left
  · intro he
    exact ⟨he,Or.inr ⟨by omega,by omega⟩⟩

end Adjacencies

 theorem fullDiagram_left_independent {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ)
    (x y : ProbePart (EvenVertex (2*p) h) (Fin h) s) :
    ¬(fullMonotoneDiagram pairs s).graph.Adj (.inl x) (.inl y) := by
  rcases x with (⟨j,u⟩ | ⟨r,a⟩) <;> rcases y with (⟨k,v⟩ | ⟨t,b⟩)
  · exact even_even_not_adj pairs j k u v
  · exact even_Q_not_adj pairs j u t b
  · intro h
    exact even_Q_not_adj pairs k v r a h.symm
  · exact Q_Q_not_adj pairs r t a b

 theorem fullDiagram_right_independent {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ)
    (x y : ProbePart (OddVertex (2*p) h) (Fin h) s) :
    ¬(fullMonotoneDiagram pairs s).graph.Adj (.inr x) (.inr y) := by
  rcases x with (⟨r,u⟩ | ⟨r,a⟩) <;> rcases y with (⟨t,v⟩ | ⟨t,b⟩)
  · exact odd_odd_not_adj pairs r t u v
  · exact odd_P_not_adj pairs r u t b
  · intro h
    exact odd_P_not_adj pairs t v r a h.symm
  · exact P_P_not_adj pairs r t a b

 theorem fullDiagram_cross_part {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ)
    (x : ProbePart (EvenVertex (2*p) h) (Fin h) s)
    (y : ProbePart (OddVertex (2*p) h) (Fin h) s) :
    (fullMonotoneDiagram pairs s).graph.Adj (.inl x) (.inr y) ↔
      probeRelation (queryRelation pairs) evenAttachment oddAttachment s x y := by
  rcases x with (⟨j,u⟩ | ⟨r,a⟩) <;> rcases y with (⟨t,v⟩ | ⟨t,b⟩)
  · exact even_odd_adj pairs j u t v
  · exact even_P_adj pairs j u t b
  · simpa only [probeRelation,oddAttachment,eq_comm] using Q_odd_adj pairs r a t v
  · exact Q_P_adj pairs r t a b

/-- Exhaustive graph equality for the actual finite integer endpoint representation. -/
theorem fullMonotoneDiagram_graph {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) :
    (fullMonotoneDiagram pairs s).graph = fullMonotoneQueryGraph pairs s := by
  ext x y
  cases x with
  | inl x =>
    cases y with
    | inl y => exact iff_false_intro (fullDiagram_left_independent pairs s x y)
    | inr y => exact fullDiagram_cross_part pairs s x y
  | inr x =>
    cases y with
    | inl y =>
      exact ⟨fun h => (fullDiagram_cross_part pairs s y x).mp h.symm,
        fun h => ((fullDiagram_cross_part pairs s y x).mpr h).symm⟩
    | inr y => exact iff_false_intro (fullDiagram_right_independent pairs s x y)

end HiddenCircuits.GraphReduction
