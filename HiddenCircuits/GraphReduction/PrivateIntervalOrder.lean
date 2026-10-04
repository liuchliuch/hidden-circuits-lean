import HiddenCircuits.GraphReduction.IntervalOrder
import HiddenCircuits.GraphReduction.PrivateProbeChordal
import HiddenCircuits.GraphReduction.CliqueProbeDecidable

/-! An explicit interval order for the literal private-clique query vertices. -/
namespace HiddenCircuits.GraphReduction.PrivateProbe

def layerIndex {h : ℕ} : Layer h → ℕ
  | .inl j =>  2*j.val
  | .inr r =>  2*r.val+1

def intervalLayer {n h s : ℕ} : Vertex n h s → ℕ
  | .inl v =>  layerNumber v
  | .inr q =>  layerIndex q.1

def intervalRank {n h s : ℕ} : Vertex n h s → ℕ
  | .inl v =>  s+eliminationRank v
  | .inr q =>  q.2.val

def intervalKey {n h s : ℕ} (v : Vertex n h s) : ℕ :=
  intervalLayer v*(n+s+1)+intervalRank v

lemma layerIndex_injective {h : ℕ} : Function.Injective (@layerIndex h) := by
  intro x y he
  rcases x with x|x  <;>  rcases y with y|y
  all_goals simp only [layerIndex] at he
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

lemma layerIndex_tag {n h : ℕ} (x : Original n h) : layerIndex (layerTag x)=layerNumber x := by
  rcases x with x|x  <;>  rfl

lemma intervalRank_lt {n h s : ℕ} (v : Vertex n h s) : intervalRank v < n+s+1 := by
  rcases v with v|q
  · have hv:=eliminationRank_le v
    simp only [intervalRank]; omega
  · simp only [intervalRank]; have := q.2.isLt; omega

lemma intervalKey_layer_le {n h s : ℕ} {x y : Vertex n h s} (hk : intervalKey x ≤ intervalKey y) :
    intervalLayer x ≤ intervalLayer y := by
  have hx:=intervalRank_lt x
  have hy:=intervalRank_lt y
  by_contra hn
  have hm:=Nat.mul_le_mul_right (n+s+1) (show intervalLayer y+1 ≤ intervalLayer x by omega)
  unfold intervalKey at hk
  nlinarith

lemma intervalKey_lt_iff {n h s : ℕ} (x y : Vertex n h s) :
    intervalKey x < intervalKey y ↔ intervalLayer x < intervalLayer y ∨
      (intervalLayer x=intervalLayer y ∧ intervalRank x < intervalRank y) := by
  have hx := intervalRank_lt x
  have hy := intervalRank_lt y
  constructor
  · intro hk
    have hl := intervalKey_layer_le (Nat.le_of_lt hk)
    rcases lt_or_eq_of_le hl with hl | hl
    · exact Or.inl hl
    · refine Or.inr ⟨hl, ?_⟩
      unfold intervalKey at hk
      rw [hl] at hk
      omega
  · rintro (hl | ⟨hl,hr⟩)
    · have hm := Nat.mul_le_mul_right (n+s+1) (show intervalLayer x+1 ≤ intervalLayer y by omega)
      unfold intervalKey
      nlinarith
    · unfold intervalKey
      rw [hl]
      omega

lemma intervalKey_same_layer {n h s : ℕ} {x y : Vertex n h s} (hl : intervalLayer x=intervalLayer y) :
    intervalKey x ≤ intervalKey y ↔ intervalRank x ≤ intervalRank y := by
  simp only [intervalKey,hl,Nat.add_le_add_iff_left]

lemma intervalKey_injective {n h s : ℕ} : Function.Injective (@intervalKey n h s) := by
  intro x y he
  have hl : intervalLayer x=intervalLayer y := Nat.le_antisymm
    (intervalKey_layer_le (Nat.le_of_eq he)) (intervalKey_layer_le (Nat.le_of_eq he.symm))
  have hr : intervalRank x=intervalRank y := by unfold intervalKey at he; rw [hl] at he; omega
  rcases x with x|⟨i,q⟩  <;>  rcases y with y|⟨j,r⟩
  · apply congrArg Sum.inl
    apply layer_rank_injective
    apply Prod.ext
    · exact hl
    · simpa only [intervalRank,Nat.add_left_cancel_iff] using hr
  · have := r.isLt
    simp only [intervalRank] at hr
    omega
  · have := q.isLt
    simp only [intervalRank] at hr
    omega
  · apply congrArg Sum.inr
    exact Prod.ext (layerIndex_injective hl) (Fin.ext hr)

lemma interval_same_layer_clique {p h s : ℕ} (pairs : Fin h → CutPair p)
    (x y : Vertex (2*p) h s) (hl : intervalLayer x=intervalLayer y) (hn : x≠y) :
    (queryGraph pairs s).Adj x y := by
  rcases x with x|⟨i,q⟩  <;>  rcases y with y|⟨j,r⟩
  · exact layer_clique pairs x y ((layer_eq_iff x y).mp hl)
      (fun he =>  hn (congrArg Sum.inl he))
  · change layerTag x=j
    apply layerIndex_injective
    rw [layerIndex_tag]
    exact hl
  · change layerTag y=i
    apply layerIndex_injective
    rw [layerIndex_tag]
    exact hl.symm
  · have hij : i=j := layerIndex_injective hl
    refine ⟨hij, ?_⟩
    intro hqr
    exact hn (congrArg Sum.inr (Prod.ext hij hqr))

lemma interval_adj_local {p h s : ℕ} (pairs : Fin h → CutPair p)
    (x y : Vertex (2*p) h s) (ha : (queryGraph pairs s).Adj x y) :
    intervalLayer x ≤ intervalLayer y+1 ∧ intervalLayer y ≤ intervalLayer x+1 := by
  rcases x with x|⟨i,q⟩  <;>  rcases y with y|⟨j,r⟩
  · exact cliqueGraph_local pairs x y ha
  · change layerTag x=j at ha
    have he:=congrArg layerIndex ha
    rw [layerIndex_tag] at he
    simp only [intervalLayer]
    omega
  · change layerTag y=i at ha
    have he:=congrArg layerIndex ha
    rw [layerIndex_tag] at he
    simp only [intervalLayer]
    omega
  · change i=j ∧ q≠r at ha
    simp only [intervalLayer,ha.1]
    omega

/-- In the right-endpoint order, every earlier neighborhood is a suffix. -/
theorem intervalKey_suffix {p h s : ℕ} (pairs : Fin h → CutPair p) :
    Interval.SuffixOrder (queryGraph pairs s) intervalKey := by
  intro x y z hxy hyz hxz
  have hlxy:=intervalKey_layer_le hxy
  have hlyz:=intervalKey_layer_le (Nat.le_of_lt hyz)
  have hloc:=interval_adj_local pairs x z hxz
  by_cases he : intervalLayer y=intervalLayer z
  · exact interval_same_layer_clique pairs y z he (fun h =>  by subst z; omega)
  have hly : intervalLayer x=intervalLayer y := by omega
  have hlz : intervalLayer z=intervalLayer x+1 := by omega
  have hr := (intervalKey_same_layer hly).mp hxy
  rcases x with x|⟨i,q⟩  <;>  rcases z with z|⟨j,r⟩
  · cases y with
    | inl y =>  exact cliqueGraph_nested pairs x y z hly (by simpa only [intervalRank,Nat.add_le_add_iff_left] using hr) hlz hxz
    | inr y =>  have := y.2.isLt; simp only [intervalRank] at hr; omega
  · change layerTag x=j at hxz
    have hh:=congrArg layerIndex hxz
    rw [layerIndex_tag] at hh
    change layerIndex j=layerNumber x+1 at hlz
    omega
  · change layerTag z=i at hxz
    have hh:=congrArg layerIndex hxz
    rw [layerIndex_tag] at hh
    change layerNumber z=layerIndex i+1 at hlz
    omega
  · change i=j ∧ q≠r at hxz
    change layerIndex j=layerIndex i+1 at hlz
    rw [hxz.1] at hlz
    omega

end HiddenCircuits.GraphReduction.PrivateProbe
