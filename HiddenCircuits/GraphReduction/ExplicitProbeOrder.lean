import HiddenCircuits.GraphReduction.PrivateProbeChordal

/-! Executable private-probe elimination positions from a supplied actual numeric label map. -/
namespace HiddenCircuits.GraphReduction
variable {V : Type*}

def explicitPrivateKey {G : SimpleGraph V} {I : Type*} {m : ℕ} {s : ℕ} (o : PerfectEliminationOrder G) (index : I ↪ Fin m)
    : V ⊕ (I × Fin s) → ℕ
  | .inl v => m*s+o.position v
  | .inr q => (finProdFinEquiv (index q.1,q.2)).val

/-- Private probe cliques preserve an actual perfect elimination order. -/
def explicitPrivateProbeOrder {G : SimpleGraph V} (o : PerfectEliminationOrder G)
    {I : Type*} {m : ℕ} (index : I ↪ Fin m) (layer : V → I)
    (hclique : ∀ v w, layer v=layer w → v≠w → G.Adj v w)
    (s : ℕ) : PerfectEliminationOrder
      (cliqueProbeGraph G (fun i v => layer v=i) s) where
  position := explicitPrivateKey o index
  injective := by
    intro x y he
    rcases x with v|a <;> rcases y with w|b
    · apply congrArg Sum.inl; apply o.injective
      change m*s+o.position v=m*s+o.position w at he
      omega
    · have hb := (finProdFinEquiv (index b.1,b.2)).isLt
      change m*s+o.position v=(finProdFinEquiv (index b.1,b.2)).val at he
      omega
    · have ha := (finProdFinEquiv (index a.1,a.2)).isLt
      change (finProdFinEquiv (index a.1,a.2)).val=m*s+o.position w at he
      omega
    · apply congrArg Sum.inr
      have hh := finProdFinEquiv.injective (Fin.ext he)
      apply Prod.ext
      · exact (index).injective (congrArg Prod.fst hh)
      · exact congrArg (fun q : Fin (m) × Fin s => q.2) hh
  later_clique := by
    intro x y z hxy hxz hpy hpz hyz
    rcases x with v|⟨i,a⟩
    · rcases y with w|b <;> rcases z with u|c
      · apply o.later_clique v w u hxy hxz
        · change m*s+o.position v<m*s+o.position w at hpy; omega
        · change m*s+o.position v<m*s+o.position u at hpz; omega
        · exact fun e => hyz (congrArg Sum.inl e)
      · have hc := (finProdFinEquiv (index c.1,c.2)).isLt
        change m*s+o.position v<(finProdFinEquiv (index c.1,c.2)).val at hpz
        omega
      · have hb := (finProdFinEquiv (index b.1,b.2)).isLt
        change m*s+o.position v<(finProdFinEquiv (index b.1,b.2)).val at hpy
        omega
      · have hb := (finProdFinEquiv (index b.1,b.2)).isLt
        change m*s+o.position v<(finProdFinEquiv (index b.1,b.2)).val at hpy
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

namespace PrivateProbe
/-- The sum of the concrete even/odd layer labels has its canonical executable numeric index. -/
def explicitLayerIndex (h : ℕ) : Layer h ↪ Fin ((h+1)+h) := finSumFinEquiv.toEmbedding

/-- The literal Section11 elimination algorithm contains no chosen finite-type enumeration. -/
def explicitRetainedQueryOrder {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) : PerfectEliminationOrder (retainedQueryGraph pairs S T s) :=
  explicitPrivateProbeOrder (retainedOriginalOrder pairs S T) (explicitLayerIndex h) (retainedLayer S T)
    (fun v w hl hn => layer_clique pairs (originalEmbedding S T v) (originalEmbedding S T w)
      hl (fun he => hn ((originalEmbedding S T).injective he))) s
end PrivateProbe
end HiddenCircuits.GraphReduction
