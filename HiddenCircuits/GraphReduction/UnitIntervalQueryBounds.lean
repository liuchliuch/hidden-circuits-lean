import HiddenCircuits.GraphReduction.UnitIntervalConcreteRepresentation

/-! Explicit integer endpoints and their polynomial magnitude bound for every query. -/
namespace HiddenCircuits.GraphReduction
open UnitInterval

def unitQueryLeftInteger {p : ℕ} (w : List (CutPair p)) {S T : State (2*p) p}
    {s : ℕ} : UnitOriginalVertex p w.length S T ⊕ (Fin (w.length+1) × Fin s) → ℤ
  | .inl v => unitOriginalLayer v*commonLength (2*p) w.length+unitOriginalOffset w v
  | .inr (r,_) => (2*(r.val:ℤ)+1)*commonLength (2*p) w.length

 theorem unitIntervalQuery_left_integer {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (s : ℕ) (v : UnitOriginalVertex p w.length S T ⊕ (Fin (w.length+1) × Fin s)) :
    (unitIntervalQueryRepresentation w S T s).left v=(unitQueryLeftInteger w v:ℚ) := by
  cases v <;> simp [unitIntervalQueryRepresentation,probeLeft,unitQueryLeftInteger]

 theorem unitOriginalLayer_bounds {p h : ℕ} {S T : State (2*p) p}
    (v : UnitOriginalVertex p h S T) : 0 ≤ unitOriginalLayer v ∧ unitOriginalLayer v ≤ 2*(h:ℤ) := by
  cases v with
  | inl v => have hv := v.val.1.isLt; simp only [unitOriginalLayer]; omega
  | inr v => have hv := v.1.isLt; simp only [unitOriginalLayer]; omega

/-- Every left and right endpoint is a nonnegative integer of explicit O((p+1)(h+1)^2) size. -/
theorem unitQuery_endpoint_bounds {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (s : ℕ) (v : UnitOriginalVertex p w.length S T ⊕ (Fin (w.length+1) × Fin s)) :
    0 ≤ unitQueryLeftInteger w v ∧
      unitQueryLeftInteger w v+commonLength (2*p) w.length ≤ 4000*(p+1)*(w.length+1)^2 := by
  have hΛ : (0:ℚ) < commonLength (2*p) w.length := by exact_mod_cast commonLength_positive (2*p) w.length
  have hh := probeLeft_bounds hΛ unitOriginalLayer (fun x => (unitOriginalOffset w x:ℚ))
    (fun r : Fin (w.length+1) => (r.val:ℤ)) w.length
    unitOriginalLayer_bounds (unitOriginalOffset_rat_inside w)
    (fun r => by have hr := r.isLt; constructor <;> dsimp <;> omega) v
  have he : probeLeft (commonLength (2*p) w.length) unitOriginalLayer
      (fun x : UnitOriginalVertex p w.length S T => (unitOriginalOffset w x:ℚ))
      (fun r : Fin (w.length+1) => (r.val:ℤ)) v = (unitQueryLeftInteger w v:ℚ) := by
    cases v <;> simp [probeLeft,unitQueryLeftInteger]
  rw [he] at hh
  have hb : (unitQueryLeftInteger w v:ℚ)+(commonLength (2*p) w.length:ℚ) ≤
      4000*((p:ℚ)+1)*((w.length:ℚ)+1)^2 := by
    calc
      _ ≤ (2*(w.length:ℚ)+2)*(commonLength (2*p) w.length:ℚ) := hh.2
      _ = _ := by unfold commonLength scale; push_cast; ring
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hb

/-- The same graph has a verified representation by intervals of literal length one. -/
def unitIntervalQueryUnitRepresentation {p : ℕ} (w : List (CutPair p))
    (S T : State (2*p) p) (s : ℕ) : Representation (unitIntervalQueryGraph (fun r => w.get r) S T s) :=
  (unitIntervalQueryRepresentation w S T s).unitLength

@[simp] theorem unitIntervalQueryUnitRepresentation_length {p : ℕ} (w : List (CutPair p))
    (S T : State (2*p) p) (s : ℕ) : (unitIntervalQueryUnitRepresentation w S T s).length=1 := rfl

end HiddenCircuits.GraphReduction
