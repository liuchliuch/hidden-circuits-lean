import HiddenCircuits.GraphReduction.PrivateProbeDiagram

/-! Exact verification of all original cuts, clique layers, and private probe adjacencies. -/
namespace HiddenCircuits.GraphReduction.PrivateProbe
section Adjacencies
variable {p h s : ℕ} (pairs : Fin h → CutPair p)

theorem even_even_adj (j k : Fin (h+1)) (u v : Fin (2*p)) :
    (diagram pairs s).graph.Adj (.inl (.inl (j,u))) (.inl (.inl (k,v))) ↔ j=k ∧ u≠v := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content]
  rw [crossing_equal_blocks]
  constructor
  · rintro ⟨hj,hc⟩
    subst k
    refine ⟨rfl,?_⟩
    intro he
    subst v
    simp at hc
  · rintro ⟨hj,hu⟩
    subst k
    refine ⟨rfl,?_⟩
    simp only [top_even_lt_iff,bottom_even_lt_iff]
    have hn : u.val≠v.val := fun he => hu (Fin.ext he)
    omega

theorem odd_odd_adj (r t : Fin h) (u v : Fin (2*p)) :
    (diagram pairs s).graph.Adj (.inl (.inr (r,u))) (.inl (.inr (t,v))) ↔ r=t ∧ u≠v := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content,
    upperModeAt_castSucc,lowerModeAt_succ]
  rw [crossing_shifted_blocks]
  constructor
  · rintro ⟨hr,hc⟩
    subst t
    refine ⟨rfl,?_⟩
    intro he
    subst v
    simp at hc
  · rintro ⟨hr,hu⟩
    subst t
    refine ⟨rfl,?_⟩
    simp only [top_odd_lt_iff,bottom_odd_lt_iff]
    have hn : u.val≠v.val := fun he => hu (Fin.ext he)
    omega

theorem even_odd_adj (j : Fin (h+1)) (r : Fin h) (u v : Fin (2*p)) :
    (diagram pairs s).graph.Adj (.inl (.inl (j,u))) (.inl (.inr (r,v))) ↔
      targetRelation pairs (j,u) (r,v) := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content,
    upperModeAt_castSucc,lowerModeAt_succ]
  rw [crossing_neighbor_blocks]
  change (_ ∧ _) ∨ (_ ∧ _) ↔ (j.val=r.val ∧ _) ∨ (j.val=r.val+1 ∧ _)
  apply or_congr
  · apply and_congr_right
    intro hj
    rw [upperModeAt_eq pairs j r hj,top_cut]
  · apply and_congr_right
    intro hj
    rw [lowerModeAt_eq pairs j r hj,bottom_cut]

theorem even_evenProbe_adj (j k : Fin (h+1)) (u : Fin (2*p)) (q : Fin s) :
    (diagram pairs s).graph.Adj (.inl (.inl (j,u))) (.inr (.inl k,q)) ↔ j=k := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content]
  rw [crossing_equal_blocks]
  constructor
  · exact And.left
  · intro hj
    subst k
    refine ⟨rfl,?_⟩
    simp only [top_even,top_evenProbe,bottom_even,bottom_evenProbe]
    have ht := (upperModeAt pairs j).evenOffset_lt u
    have hb := (lowerModeAt pairs j).evenOffset_lt u
    have hq := q.isLt
    omega

theorem odd_oddProbe_adj (r t : Fin h) (u : Fin (2*p)) (q : Fin s) :
    (diagram pairs s).graph.Adj (.inl (.inr (r,u))) (.inr (.inr t,q)) ↔ r=t := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content,
    upperModeAt_castSucc,lowerModeAt_succ]
  rw [crossing_shifted_blocks]
  constructor
  · exact And.left
  · intro hr
    subst t
    refine ⟨rfl,?_⟩
    simp only [top_odd,top_oddProbe,bottom_odd,bottom_oddProbe]
    have ht := (pairs r).upperMode.oddOffset_lt u
    have hb := (pairs r).lowerMode.oddOffset_lt u
    have hq := q.isLt
    omega

theorem even_oddProbe_not_adj (j : Fin (h+1)) (r : Fin h) (u : Fin (2*p)) (q : Fin s) :
    ¬(diagram pairs s).graph.Adj (.inl (.inl (j,u))) (.inr (.inr r,q)) := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content]
  rw [crossing_neighbor_blocks]
  simp only [top_even,top_oddProbe,bottom_even,bottom_oddProbe]
  have ht := (upperModeAt pairs j).evenOffset_lt u
  have hb := (lowerModeAt pairs j).evenOffset_lt u
  have hq := q.isLt
  omega

theorem evenProbe_odd_not_adj (j : Fin (h+1)) (r : Fin h) (u : Fin (2*p)) (q : Fin s) :
    ¬(diagram pairs s).graph.Adj (.inr (.inl j,q)) (.inl (.inr (r,u))) := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content,
    upperModeAt_castSucc,lowerModeAt_succ]
  rw [crossing_neighbor_blocks]
  simp only [top_evenProbe,top_odd,bottom_evenProbe,bottom_odd]
  have ht := (pairs r).upperMode.oddOffset_lt u
  have hb := (pairs r).lowerMode.oddOffset_lt u
  have hq := q.isLt
  omega

theorem evenProbe_evenProbe_adj (j k : Fin (h+1)) (q t : Fin s) :
    (diagram pairs s).graph.Adj (.inr (.inl j,q)) (.inr (.inl k,t)) ↔ j=k ∧ q≠t := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content]
  rw [crossing_equal_blocks]
  simp only [top_evenProbe,bottom_evenProbe,ne_eq,Fin.ext_iff]
  have hq := q.isLt
  have ht := t.isLt
  omega

theorem oddProbe_oddProbe_adj (r t : Fin h) (q z : Fin s) :
    (diagram pairs s).graph.Adj (.inr (.inr r,q)) (.inr (.inr t,z)) ↔ r=t ∧ q≠z := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content]
  rw [crossing_shifted_blocks]
  simp only [top_oddProbe,bottom_oddProbe,ne_eq,Fin.ext_iff]
  have hq := q.isLt
  have hz := z.isLt
  omega

theorem evenProbe_oddProbe_not_adj (j : Fin (h+1)) (r : Fin h) (q t : Fin s) :
    ¬(diagram pairs s).graph.Adj (.inr (.inl j,q)) (.inr (.inr r,t)) := by
  simp only [diagram_adj,upperPosition,lowerPosition,topBlock,bottomBlock,content]
  rw [crossing_neighbor_blocks]
  simp only [top_evenProbe,top_oddProbe,bottom_evenProbe,bottom_oddProbe]
  have hq := q.isLt
  have ht := t.isLt
  omega

end Adjacencies

/-- The explicit endpoint diagram represents exactly the actual private-clique-probe graph. -/
theorem diagram_graph {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) :
    (diagram pairs s).graph=queryGraph pairs s := by
  ext x y
  rcases x with (⟨j,u⟩|⟨r,u⟩)|⟨j|r,q⟩ <;>
    rcases y with (⟨k,v⟩|⟨t,v⟩)|⟨k|t,z⟩
  · exact even_even_adj pairs j k u v
  · exact even_odd_adj pairs j t u v
  · simpa [queryGraph,cliqueProbeGraph,layerTag] using even_evenProbe_adj pairs j k u z
  · simpa [queryGraph,cliqueProbeGraph,layerTag] using even_oddProbe_not_adj (s:=s) pairs j t u z
  · rw [(diagram pairs s).graph.adj_comm]
    exact even_odd_adj pairs k r v u
  · exact odd_odd_adj pairs r t u v
  · rw [(diagram pairs s).graph.adj_comm]
    simpa [queryGraph,cliqueProbeGraph,layerTag] using evenProbe_odd_not_adj (s:=s) pairs k r u z
  · simpa [queryGraph,cliqueProbeGraph,layerTag] using odd_oddProbe_adj pairs r t u z
  · rw [(diagram pairs s).graph.adj_comm]
    simpa [queryGraph,cliqueProbeGraph,layerTag] using even_evenProbe_adj pairs k j v q
  · simpa [queryGraph,cliqueProbeGraph,layerTag] using evenProbe_odd_not_adj (s:=s) pairs j t v q
  · simpa [queryGraph,cliqueProbeGraph] using evenProbe_evenProbe_adj pairs j k q z
  · simpa [queryGraph,cliqueProbeGraph] using evenProbe_oddProbe_not_adj (s:=s) pairs j t q z
  · rw [(diagram pairs s).graph.adj_comm]
    simpa [queryGraph,cliqueProbeGraph,layerTag] using even_oddProbe_not_adj (s:=s) pairs k r v q
  · rw [(diagram pairs s).graph.adj_comm]
    simpa [queryGraph,cliqueProbeGraph,layerTag] using odd_oddProbe_adj pairs t r v q
  · rw [(diagram pairs s).graph.adj_comm]
    simpa [queryGraph,cliqueProbeGraph] using evenProbe_oddProbe_not_adj (s:=s) pairs k r z q
  · simpa [queryGraph,cliqueProbeGraph] using oddProbe_oddProbe_adj pairs r t q z

end HiddenCircuits.GraphReduction.PrivateProbe
