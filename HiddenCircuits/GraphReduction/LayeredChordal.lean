import HiddenCircuits.GraphReduction.CliqueProbeGraph
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Tactic

/-! Concrete elimination orders for nested consecutive clique layers. -/
namespace HiddenCircuits.GraphReduction

/-- An injective integer elimination position, with the actual later-neighbor clique property. -/
structure PerfectEliminationOrder {V : Type*} (G : SimpleGraph V) where
  position : V → ℕ
  injective : Function.Injective position
  later_clique : ∀ x y z, G.Adj x y → G.Adj x z →
    position x < position y → position x < position z → y≠z → G.Adj y z


/-- Chordality in the usual forbidden-induced-cycle sense. -/
def Chordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, 4≤n → IsEmpty ((SimpleGraph.cycleGraph n) ↪g G)

theorem sub_val_explicit {n : ℕ} (a b : Fin n) :
  (a-b).val = if b.val≤a.val then a.val-b.val else n-b.val+a.val := by
  split_ifs with h
  · exact Fin.sub_val_of_le h
  · rw [Fin.val_sub, Nat.mod_eq_of_lt (by omega)]

theorem cycle_neighbors_nonadjacent {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    ∃ a b : Fin n, (SimpleGraph.cycleGraph n).Adj i a ∧
      (SimpleGraph.cycleGraph n).Adj i b ∧ a≠b ∧
      ¬(SimpleGraph.cycleGraph n).Adj a b := by
  let a : Fin n := ⟨if i.val=0 then n-1 else i.val-1,by split <;> omega⟩
  let b : Fin n := ⟨if i.val+1<n then i.val+1 else 0,by split <;> omega⟩
  refine ⟨a,b,?_,?_,?_,?_⟩
  all_goals simp only [SimpleGraph.cycleGraph_adj',sub_val_explicit,Fin.ext_iff,ne_eq,a,b]
  all_goals split_ifs <;> omega

/-- A real perfect elimination order excludes every induced cycle of length at least four. -/
theorem PerfectEliminationOrder.chordal {V : Type*} {G : SimpleGraph V}
    (o : PerfectEliminationOrder G) : Chordal G := by
  intro n hn
  letI : NeZero n := ⟨by omega⟩
  constructor
  intro e
  obtain ⟨i,hmin⟩ := Finite.exists_min (fun j : Fin n => o.position (e j))
  obtain ⟨a,b,hia,hib,hab,hnab⟩ := cycle_neighbors_nonadjacent hn i
  have hia' : G.Adj (e i) (e a) := e.map_adj_iff.mpr hia
  have hib' : G.Adj (e i) (e b) := e.map_adj_iff.mpr hib
  have hpa : o.position (e i)<o.position (e a) := by
    have := hmin a
    have hne : o.position (e i)≠o.position (e a) := fun h => hia'.ne (o.injective h)
    omega
  have hpb : o.position (e i)<o.position (e b) := by
    have := hmin b
    have hne : o.position (e i)≠o.position (e b) := fun h => hib'.ne (o.injective h)
    omega
  exact hnab (e.map_adj_iff.mp (o.later_clique (e i) (e a) (e b) hia' hib' hpa hpb
    (fun h => hab (e.injective h))))

namespace LayeredChordal
variable {V : Type*}

def key (layer rank : V → ℕ) (R : ℕ) (v : V) := layer v*(R+1)+rank v

theorem key_layer_le {layer rank : V → ℕ} {R : ℕ} (hr : ∀ v, rank v≤R)
    {x y : V} (h : key layer rank R x ≤ key layer rank R y) : layer x≤layer y := by
  unfold key at h
  by_contra hn
  have : layer y+1≤layer x := by omega
  have := Nat.mul_le_mul_right (R+1) this
  have := hr y
  nlinarith

theorem key_injective {layer rank : V → ℕ} {R : ℕ} (hr : ∀ v, rank v≤R)
    (hi : Function.Injective (fun v => (layer v,rank v))) :
    Function.Injective (key layer rank R) := by
  intro x y h
  have hxy := key_layer_le hr h.le
  have hyx := key_layer_le hr h.ge
  have hl : layer x=layer y := by omega
  apply hi
  apply Prod.ext hl
  change rank x=rank y
  unfold key at h
  rw [hl] at h
  omega

/-- Order each clique layer by increasing inclusion of its next-layer neighborhoods. -/
def eliminationOrder {G : SimpleGraph V} (layer rank : V → ℕ) (R : ℕ)
    (hr : ∀ v, rank v≤R) (hi : Function.Injective (fun v => (layer v,rank v)))
    (hlocal : ∀ x y, G.Adj x y → layer x≤layer y+1 ∧ layer y≤layer x+1)
    (hclique : ∀ x y, layer x=layer y → x≠y → G.Adj x y)
    (hnest : ∀ x y z, layer x=layer y → rank x≤rank y →
      layer z=layer x+1 → G.Adj x z → G.Adj y z) : PerfectEliminationOrder G where
  position := key layer rank R
  injective := key_injective hr hi
  later_clique := by
    intro x y z hxy hxz hky hkz hyz
    have hly := key_layer_le hr hky.le
    have hlz := key_layer_le hr hkz.le
    have hby := (hlocal x y hxy).2
    have hbz := (hlocal x z hxz).2
    have hyr : layer y=layer x → rank x≤rank y := by
      intro h
      unfold key at hky
      rw [h] at hky
      omega
    have hzr : layer z=layer x → rank x≤rank z := by
      intro h
      unfold key at hkz
      rw [h] at hkz
      omega
    by_cases hlyx : layer y=layer x
    · by_cases hlzx : layer z=layer x
      · exact hclique y z (hlyx.trans hlzx.symm) hyz
      · exact hnest x y z hlyx.symm (hyr hlyx) (by omega) hxz
    · by_cases hlzx : layer z=layer x
      · exact G.adj_symm (hnest x z y hlzx.symm (hzr hlzx) (by omega) hxy)
      · exact hclique y z (by omega) hyz


/-- Put every private probe before all original vertices. -/
noncomputable def privateKey {G : SimpleGraph V} {I : Type*} [Fintype I] {s : ℕ} (o : PerfectEliminationOrder G)
    : V ⊕ (I × Fin s) → ℕ
  | .inl v => Fintype.card I*s+o.position v
  | .inr q => (finProdFinEquiv (Fintype.equivFin I q.1,q.2)).val

/-- Private probe cliques preserve an actual perfect elimination order. -/
noncomputable def privateProbeOrder {G : SimpleGraph V} (o : PerfectEliminationOrder G)
    {I : Type*} [Fintype I] (layer : V → I)
    (hclique : ∀ v w, layer v=layer w → v≠w → G.Adj v w)
    (s : ℕ) : PerfectEliminationOrder
      (cliqueProbeGraph G (fun i v => layer v=i) s) where
  position := privateKey o
  injective := by
    intro x y he
    rcases x with v|a <;> rcases y with w|b
    · apply congrArg Sum.inl; apply o.injective
      change Fintype.card I*s+o.position v=Fintype.card I*s+o.position w at he
      omega
    · have hb := (finProdFinEquiv (Fintype.equivFin I b.1,b.2)).isLt
      change Fintype.card I*s+o.position v=(finProdFinEquiv (Fintype.equivFin I b.1,b.2)).val at he
      omega
    · have ha := (finProdFinEquiv (Fintype.equivFin I a.1,a.2)).isLt
      change (finProdFinEquiv (Fintype.equivFin I a.1,a.2)).val=Fintype.card I*s+o.position w at he
      omega
    · apply congrArg Sum.inr
      have hh := finProdFinEquiv.injective (Fin.ext he)
      apply Prod.ext
      · exact (Fintype.equivFin I).injective (congrArg Prod.fst hh)
      · exact congrArg (fun q : Fin (Fintype.card I) × Fin s => q.2) hh
  later_clique := by
    intro x y z hxy hxz hpy hpz hyz
    rcases x with v|⟨i,a⟩
    · rcases y with w|b <;> rcases z with u|c
      · apply o.later_clique v w u hxy hxz
        · change Fintype.card I*s+o.position v<Fintype.card I*s+o.position w at hpy; omega
        · change Fintype.card I*s+o.position v<Fintype.card I*s+o.position u at hpz; omega
        · exact fun e => hyz (congrArg Sum.inl e)
      · have hc := (finProdFinEquiv (Fintype.equivFin I c.1,c.2)).isLt
        change Fintype.card I*s+o.position v<(finProdFinEquiv (Fintype.equivFin I c.1,c.2)).val at hpz
        omega
      · have hb := (finProdFinEquiv (Fintype.equivFin I b.1,b.2)).isLt
        change Fintype.card I*s+o.position v<(finProdFinEquiv (Fintype.equivFin I b.1,b.2)).val at hpy
        omega
      · have hb := (finProdFinEquiv (Fintype.equivFin I b.1,b.2)).isLt
        change Fintype.card I*s+o.position v<(finProdFinEquiv (Fintype.equivFin I b.1,b.2)).val at hpy
        omega
    · rcases y with w|⟨j,b⟩ <;> rcases z with u|⟨k,c⟩
      · change layer w=i at hxy
        change layer u=i at hxz
        exact hclique w u (hxy.trans hxz.symm) (fun e => hyz (congrArg Sum.inl e))
      · exact hxy.trans hxz.1
      · exact hxz.trans hxy.1
      · refine ⟨hxy.1.symm.trans hxz.1,?_⟩
        intro hbc
        apply hyz
        congr 1
        exact Prod.ext (hxy.1.symm.trans hxz.1) hbc

end LayeredChordal
end HiddenCircuits.GraphReduction
