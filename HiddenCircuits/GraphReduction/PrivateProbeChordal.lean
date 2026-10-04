import HiddenCircuits.GraphReduction.PrivateProbeVertices
import HiddenCircuits.GraphReduction.CutRowNesting

/-! Actual perfect elimination orders and chordality for the Section11 query family. -/
namespace HiddenCircuits.GraphReduction.PrivateProbe

def eliminationRank {n h : ℕ} : Original n h → ℕ
  | .inl (_,u) => n-1-u.val
  | .inr (_,u) => u.val

theorem eliminationRank_le {n h : ℕ} (x : Original n h) : eliminationRank x≤n := by
  rcases x with ⟨j,u⟩|⟨r,u⟩ <;> simp only [eliminationRank] <;> omega

theorem layer_rank_injective {n h : ℕ} :
    Function.Injective (fun x : Original n h => (layerNumber x,eliminationRank x)) := by
  intro x y he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  rcases x with ⟨j,u⟩|⟨r,u⟩ <;> rcases y with ⟨k,v⟩|⟨t,v⟩
  all_goals simp only [layerNumber,eliminationRank] at h1 h2
  · have hj : j=k := Fin.ext (by omega)
    have hu : u=v := Fin.ext (by have := u.isLt; have := v.isLt; omega)
    simp [hj,hu]
  · omega
  · omega
  · have hr : r=t := Fin.ext (by omega)
    have hu : u=v := Fin.ext (by omega)
    simp [hr,hu]

theorem layer_eq_iff {n h : ℕ} (x y : Original n h) : layerNumber x=layerNumber y ↔ layerTag x=layerTag y := by
  rcases x with ⟨j,u⟩|⟨r,u⟩ <;> rcases y with ⟨k,v⟩|⟨t,v⟩
  · change 2*j.val=2*k.val ↔ Sum.inl j=Sum.inl k
    simp only [Sum.inl.injEq,Fin.ext_iff]; omega
  · constructor
    · change 2*j.val=2*t.val+1 → _
      intro he; omega
    · intro he; cases he
  · constructor
    · change 2*r.val+1=2*k.val → _
      intro he; omega
    · intro he; cases he
  · change 2*r.val+1=2*t.val+1 ↔ Sum.inr r=Sum.inr t
    simp only [Sum.inr.injEq,Fin.ext_iff]; omega

theorem cliqueGraph_local {p h : ℕ} (pairs : Fin h → CutPair p) (x y : Original (2*p) h)
    (ha : (cliqueGraph pairs).Adj x y) : layerNumber x≤layerNumber y+1 ∧ layerNumber y≤layerNumber x+1 := by
  rcases x with ⟨j,u⟩|⟨r,u⟩ <;> rcases y with ⟨k,v⟩|⟨t,v⟩ <;>
    simp only [cliqueGraph,targetRelation,layerNumber] at *
  · rcases ha with ⟨rfl,_⟩; omega
  · rcases ha with h|h <;> omega
  · rcases ha with h|h <;> omega
  · rcases ha with ⟨rfl,_⟩; omega

theorem layer_clique {p h : ℕ} (pairs : Fin h → CutPair p) (x y : Original (2*p) h)
    (hl : layerTag x=layerTag y) (hne : x≠y) : (cliqueGraph pairs).Adj x y := by
  rcases x with ⟨j,u⟩|⟨r,u⟩ <;> rcases y with ⟨k,v⟩|⟨t,v⟩ <;>
    simp only [layerTag,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at hl
  · subst k; exact ⟨rfl,by intro he; subst v; exact hne rfl⟩
  · subst t; exact ⟨rfl,by intro he; subst v; exact hne rfl⟩

theorem cliqueGraph_nested {p h : ℕ} (pairs : Fin h → CutPair p)
    (x y z : Original (2*p) h) (hl : layerNumber x=layerNumber y)
    (hr : eliminationRank x≤eliminationRank y) (hz : layerNumber z=layerNumber x+1)
    (hxz : (cliqueGraph pairs).Adj x z) : (cliqueGraph pairs).Adj y z := by
  rcases x with ⟨j,u⟩|⟨r,u⟩ <;> rcases y with ⟨k,v⟩|⟨t,v⟩ <;>
    rcases z with ⟨l,w⟩|⟨s,w⟩
  all_goals simp only [layerNumber,eliminationRank] at hl hr hz
  all_goals try omega
  · have hj : j=k := Fin.ext (by omega)
    subst k
    change targetRelation pairs (j,u) (s,w) at hxz
    change targetRelation pairs (j,v) (s,w)
    simp only [targetRelation,Prod.fst,Prod.snd] at hxz ⊢
    rcases hxz with h|h
    · exact Or.inl ⟨h.1,(pairs s).first_rows_nested v u w (by have := u.isLt; have := v.isLt; omega) h.2⟩
    · omega
  · have ht : r=t := Fin.ext (by omega)
    subst t
    change targetRelation pairs (l,w) (r,u) at hxz
    change targetRelation pairs (l,w) (r,v)
    simp only [targetRelation,Prod.fst,Prod.snd] at hxz ⊢
    rcases hxz with h|h
    · omega
    · exact Or.inr ⟨h.1,(pairs r).second_rows_nested u v w hr h.2⟩

def originalOrder {p h : ℕ} (pairs : Fin h → CutPair p) : PerfectEliminationOrder (cliqueGraph pairs) :=
  LayeredChordal.eliminationOrder layerNumber eliminationRank (2*p) eliminationRank_le
    layer_rank_injective (cliqueGraph_local pairs)
    (fun x y hl hn => layer_clique pairs x y ((layer_eq_iff x y).mp hl) hn)
    (cliqueGraph_nested pairs)

noncomputable def queryOrder {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) :
    PerfectEliminationOrder (queryGraph pairs s) :=
  LayeredChordal.privateProbeOrder (originalOrder pairs) layerTag (layer_clique pairs) s

theorem queryGraph_chordal {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ) :
    Chordal (queryGraph pairs s) := (queryOrder pairs s).chordal


def retainedOriginalOrder {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    PerfectEliminationOrder (retainedCliqueGraph pairs S T) where
  position := fun v => (originalOrder pairs).position (originalEmbedding S T v)
  injective := (originalOrder pairs).injective.comp (originalEmbedding S T).injective
  later_clique := by
    intro x y z hxy hxz hpy hpz hyz
    exact (originalOrder pairs).later_clique _ _ _ hxy hxz hpy hpz
      (fun he => hyz ((originalEmbedding S T).injective he))

noncomputable def retainedQueryOrder {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) : PerfectEliminationOrder (retainedQueryGraph pairs S T s) :=
  LayeredChordal.privateProbeOrder (retainedOriginalOrder pairs S T) (retainedLayer S T)
    (fun v w hl hn => layer_clique pairs (originalEmbedding S T v) (originalEmbedding S T w)
      hl (fun he => hn ((originalEmbedding S T).injective he))) s

theorem retainedQueryGraph_chordal {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) : Chordal (retainedQueryGraph pairs S T s) :=
  (retainedQueryOrder pairs S T s).chordal

end HiddenCircuits.GraphReduction.PrivateProbe
