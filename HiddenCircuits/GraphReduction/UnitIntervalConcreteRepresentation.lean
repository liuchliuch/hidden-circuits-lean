import HiddenCircuits.GraphReduction.UnitIntervalLayerProfiles
import HiddenCircuits.GraphReduction.UnitIntervalParityGeometry
import HiddenCircuits.GraphReduction.UnitIntervalProbeRepresentation
import HiddenCircuits.GraphReduction.UnitIntervalGraphs
import HiddenCircuits.PairedLayerGraph

/-! Actual integer profile endpoints represent the precise Section10 query graphs. -/
namespace HiddenCircuits.GraphReduction
open UnitInterval

/-- Literal integer offset assigned to each retained original vertex. -/
def unitOriginalOffset {p : ℕ} (w : List (CutPair p)) {S T : State (2*p) p} :
    UnitOriginalVertex p w.length S T → ℤ
  | .inl x => layerProfile (scale w.length) (initialProfile (2*p) (scale w.length)) w
      ⟨2*x.val.1.val,by have := x.val.1.isLt; omega⟩ x.val.2
  | .inr y => layerProfile (scale w.length) (initialProfile (2*p) (scale w.length)) w
      ⟨2*y.1.val+1,by have := y.1.isLt; omega⟩ y.2

 theorem unitOriginalOffset_inside {p : ℕ} (w : List (CutPair p)) {S T : State (2*p) p}
    (v : UnitOriginalVertex p w.length S T) :
    0 < unitOriginalOffset w (S := S) (T := T) v ∧ unitOriginalOffset w (S := S) (T := T) v < commonLength (2*p) w.length := by
  cases v <;> exact layerProfile_inside w (le_refl _) _ _

 theorem unitOriginalOffset_first {p : ℕ} (w : List (CutPair p)) {S T : State (2*p) p}
    (x : RetainedEven p w.length S T) (y : OddVertex (2*p) w.length)
    (he : x.val.1.val=y.1.val) :
    unitOriginalOffset w (S := S) (T := T) (.inr y) ≤ unitOriginalOffset w (S := S) (T := T) (.inl x) ↔
      (w.get y.1).first x.val.2 y.2=0 := by
  simpa only [unitOriginalOffset,he] using
    layerProfile_first_cut w (le_refl _) y.1.val y.1.isLt x.val.2 y.2

 theorem unitOriginalOffset_second {p : ℕ} (w : List (CutPair p)) {S T : State (2*p) p}
    (x : RetainedEven p w.length S T) (y : OddVertex (2*p) w.length)
    (he : x.val.1.val=y.1.val+1) :
    unitOriginalOffset w (S := S) (T := T) (.inl x) ≤ unitOriginalOffset w (S := S) (T := T) (.inr y) ↔
      (w.get y.1).second y.2 x.val.2=1 := by
  simpa only [unitOriginalOffset,he] using
    layerProfile_second_cut w (le_refl _) y.1.val y.1.isLt y.2 x.val.2

 theorem commonLength_positive (n h : ℕ) : 0 < commonLength n h := by
  unfold commonLength
  have hh : 0 < scale h := by have := scale_positive h; omega
  positivity

 theorem unit_cross_intervals {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (x : RetainedEven p w.length S T) (y : OddVertex (2*p) w.length) :
    (interval (commonLength (2*p) w.length) (unitOriginalLayer (S := S) (T := T) (.inl x)) (unitOriginalOffset w (S := S) (T := T) (.inl x)) ∩
      interval (commonLength (2*p) w.length) (unitOriginalLayer (S := S) (T := T) (.inr y)) (unitOriginalOffset w (S := S) (T := T) (.inr y))).Nonempty ↔
      unitIntervalCrossRelation (fun r => w.get r) S T x y := by
  have hΛ : (0:ℚ) < commonLength (2*p) w.length := by exact_mod_cast commonLength_positive (2*p) w.length
  have hx : (0:ℚ) < (unitOriginalOffset w (S := S) (T := T) (.inl x):ℚ) ∧
      (unitOriginalOffset w (S := S) (T := T) (.inl x):ℚ) < commonLength (2*p) w.length := by
    exact_mod_cast unitOriginalOffset_inside w (S := S) (T := T) (.inl x)
  have hy : (0:ℚ) < (unitOriginalOffset w (S := S) (T := T) (.inr y):ℚ) ∧
      (unitOriginalOffset w (S := S) (T := T) (.inr y):ℚ) < commonLength (2*p) w.length := by
    exact_mod_cast unitOriginalOffset_inside w (S := S) (T := T) (.inr y)
  rw [unitOriginalLayer,unitOriginalLayer,evenOdd_overlap hΛ hx hy]
  have he0 : (x.val.1.val:ℤ)=y.1.val ↔ x.val.1.val=y.1.val := by omega
  have he1 : (x.val.1.val:ℤ)=(y.1.val:ℤ)+1 ↔ x.val.1.val=y.1.val+1 := by omega
  rw [he0,he1]
  unfold unitIntervalCrossRelation
  apply or_congr
  · apply and_congr_right
    intro he
    have hh := unitOriginalOffset_first w x y he
    have hz := (w.get y.1).first_zero_one x.val.2 y.2
    have hcast : ((unitOriginalOffset w (S := S) (T := T) (.inr y):ℚ) ≤ (unitOriginalOffset w (S := S) (T := T) (.inl x):ℚ)) ↔
        unitOriginalOffset w (S := S) (T := T) (.inr y) ≤ unitOriginalOffset w (S := S) (T := T) (.inl x) := by norm_cast
    rw [hcast,hh]
    rcases hz with hz|hz <;> change ((w.get y.1).first x.val.2 y.2=0 ↔ (w.get y.1).first x.val.2 y.2≠1) <;> rw [hz] <;> norm_num
  · apply and_congr_right
    intro he
    have hcast : ((unitOriginalOffset w (S := S) (T := T) (.inl x):ℚ) ≤ (unitOriginalOffset w (S := S) (T := T) (.inr y):ℚ)) ↔
        unitOriginalOffset w (S := S) (T := T) (.inl x) ≤ unitOriginalOffset w (S := S) (T := T) (.inr y) := by norm_cast
    rw [hcast,unitOriginalOffset_second w x y he]

theorem unitOriginalOffset_rat_inside {p : ℕ} (w : List (CutPair p)) {S T : State (2*p) p}
    (v : UnitOriginalVertex p w.length S T) :
    (0:ℚ) < unitOriginalOffset w v ∧ (unitOriginalOffset w v:ℚ) < commonLength (2*p) w.length := by
  exact_mod_cast unitOriginalOffset_inside w v

/-- The original graph is exactly the intersection graph of its explicitly emitted integer profiles. -/
theorem unitOriginal_intervals {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (x y : UnitOriginalVertex p w.length S T) :
    (unitIntervalOriginalGraph (fun r => w.get r) S T).Adj x y ↔ x≠y ∧
      (interval (commonLength (2*p) w.length) (unitOriginalLayer x) (unitOriginalOffset w x) ∩
        interval (commonLength (2*p) w.length) (unitOriginalLayer y) (unitOriginalOffset w y)).Nonempty := by
  have hΛ : (0:ℚ) < commonLength (2*p) w.length := by exact_mod_cast commonLength_positive (2*p) w.length
  have hx := unitOriginalOffset_rat_inside w x
  have hy := unitOriginalOffset_rat_inside w y
  rcases x with x|x <;> rcases y with y|y
  · have hh := sameParity_overlap hΛ hx hy (x.val.1.val:ℤ) (y.val.1.val:ℤ) 0
    simp only [add_zero] at hh
    change _ ↔ _ ∧ (interval _ (2*(x.val.1.val:ℤ)) _ ∩ interval _ (2*(y.val.1.val:ℤ)) _).Nonempty
    rw [hh]
    change (x.val.1=y.val.1 ∧ x.val.2≠y.val.2) ↔ Sum.inl x≠Sum.inl y ∧ (x.val.1.val:ℤ)=y.val.1.val
    constructor
    · rintro ⟨hl,ht⟩
      exact ⟨fun he => ht (congrArg (fun z : RetainedEven p w.length S T => z.val.2) (Sum.inl.inj he)),by simp [hl]⟩
    · rintro ⟨hne,hl⟩
      have hl' : x.val.1=y.val.1 := Fin.ext (by exact_mod_cast hl)
      refine ⟨hl',?_⟩
      intro ht
      apply hne
      congr 1
      exact Subtype.ext (Prod.ext hl' ht)
  · rw [unit_cross_intervals w S T x y]
    simp [unitIntervalOriginalGraph]
  · rw [Set.inter_comm,unit_cross_intervals w S T y x]
    simp [unitIntervalOriginalGraph]
  · have hh := sameParity_overlap hΛ hx hy (x.1.val:ℤ) (y.1.val:ℤ) 1
    change _ ↔ _ ∧ (interval _ (2*(x.1.val:ℤ)+1) _ ∩ interval _ (2*(y.1.val:ℤ)+1) _).Nonempty
    rw [hh]
    change (x.1=y.1 ∧ x.2≠y.2) ↔ Sum.inr x≠Sum.inr y ∧ (x.1.val:ℤ)=y.1.val
    constructor
    · rintro ⟨hl,ht⟩
      exact ⟨fun he => ht (congrArg Prod.snd (Sum.inr.inj he)),by simp [hl]⟩
    · rintro ⟨hne,hl⟩
      have hl' : x.1=y.1 := Fin.ext (by exact_mod_cast hl)
      exact ⟨hl',fun ht => hne (congrArg Sum.inr (Prod.ext hl' ht))⟩

 theorem unitAttachment_layer {p h : ℕ} (S T : State (2*p) p) (r : Fin (h+1))
    (v : UnitOriginalVertex p h S T) :
    unitIntervalAttachment S T r v ↔ unitOriginalLayer v=2*(r.val:ℤ) ∨
      unitOriginalLayer v=2*(r.val:ℤ)+1 := by
  cases v <;> simp only [unitIntervalAttachment,unitOriginalLayer,Fin.ext_iff,Fin.val_castSucc] <;> omega

/-- A concrete equal-length representation of each simple unweighted oracle graph. -/
def unitIntervalQueryRepresentation {p : ℕ} (w : List (CutPair p))
    (S T : State (2*p) p) (s : ℕ) :
    UnitInterval.Representation (unitIntervalQueryGraph (fun r => w.get r) S T s) := by
  have hΛ : (0:ℚ) < commonLength (2*p) w.length := by exact_mod_cast commonLength_positive (2*p) w.length
  have he : unitIntervalAttachment S T =
      (fun (r : Fin (w.length+1)) (v : UnitOriginalVertex p w.length S T) =>
        unitOriginalLayer v=2*(r.val:ℤ) ∨ unitOriginalLayer v=2*(r.val:ℤ)+1) := by
    funext r v
    exact propext (unitAttachment_layer S T r v)
  refine { length := commonLength (2*p) w.length
           positive := hΛ
           left := probeLeft (commonLength (2*p) w.length) unitOriginalLayer
             (fun v => (unitOriginalOffset w v:ℚ)) (fun r : Fin (w.length+1) => (r.val:ℤ))
           adjacency := ?_ }
  intro x y
  have hh := probeLeft_adj hΛ unitOriginalLayer (fun v => (unitOriginalOffset w v:ℚ))
    (fun r : Fin (w.length+1) => (r.val:ℤ))
    (fun i j h => Fin.ext (by change (i.val:ℤ)=(j.val:ℤ) at h; exact_mod_cast h))
    (unitOriginalOffset_rat_inside w) (unitOriginal_intervals w S T) s x y
  rw [← he] at hh
  exact hh

end HiddenCircuits.GraphReduction
