import HiddenCircuits.GraphReduction.UnitIntervalProfiles

/-! The actual recursively emitted integer profiles stay separated and inside their common length. -/
namespace HiddenCircuits.GraphReduction.UnitInterval

def scale (h : ℕ) : ℤ := 1000*(h+1)
def commonLength (n h : ℕ) : ℤ := (n+2)*scale h

def initialProfile (n : ℕ) (δ : ℤ) : Profile n := fun v => (v.val+1)*δ

def runOutput {p : ℕ} (a : Profile (2*p)) : List (CutPair p) → Profile (2*p)
  | [] => a
  | P::w => runOutput (outputProfile a P) w

def inputProfile {p : ℕ} (h : ℕ) (w : List (CutPair p)) : Profile (2*p) :=
  runOutput (initialProfile (2*p) (scale h)) w

 theorem outputProfile_displacement {p : ℕ} (a : Profile (2*p)) (P : CutPair p)
    (v : Fin (2*p)) : a v-2 ≤ outputProfile a P v ∧ outputProfile a P v ≤ a v+2 := by
  cases P  <;>  simp only [outputProfile]
  all_goals first | omega | split_ifs  <;>  omega

 theorem runOutput_displacement {p : ℕ} (a : Profile (2*p)) (w : List (CutPair p))
    (v : Fin (2*p)) : a v-2*w.length ≤ runOutput a w v ∧ runOutput a w v ≤ a v+2*w.length := by
  induction w generalizing a with
  | nil => simp [runOutput]
  | cons P w ih =>
    have hh := ih (outputProfile a P)
    have hd := outputProfile_displacement a P v
    simp only [runOutput,List.length_cons,Int.natCast_add,Int.natCast_one]
    omega

 theorem inputProfile_displacement {p h : ℕ} (w : List (CutPair p)) (hw : w.length ≤ h)
    (v : Fin (2*p)) :
    (v.val+1)*scale h-2*h ≤ inputProfile h w v ∧
      inputProfile h w v ≤ (v.val+1)*scale h+2*h := by
  have hh := runOutput_displacement (initialProfile (2*p) (scale h)) w v
  have hc : (w.length:ℤ) ≤ h := by exact_mod_cast hw
  change (v.val+1)*scale h-2*w.length ≤ inputProfile h w v ∧
    inputProfile h w v ≤ (v.val+1)*scale h+2*w.length at hh
  omega

 theorem scale_positive (h : ℕ) : 8 ≤ scale h := by unfold scale; omega

 theorem inputProfile_separated {p h : ℕ} (w : List (CutPair p)) (hw : w.length ≤ h) :
    Separated (inputProfile h w) := by
  intro u v huv
  have hu := inputProfile_displacement w hw u
  have hv := inputProfile_displacement w hw v
  have hc : (u.val:ℤ)+1 ≤ v.val := by exact_mod_cast huv
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ scale h by have := scale_positive h; omega)
  unfold scale at *
  nlinarith

/-- Input bounds uniform over every track and every prefix of the pair word. -/
theorem inputProfile_bounds {p h : ℕ} (w : List (CutPair p)) (hw : w.length ≤ h)
    (v : Fin (2*p)) :
    scale h-2*h ≤ inputProfile h w v ∧ inputProfile h w v ≤ (2*p)*scale h+2*h := by
  have hh := inputProfile_displacement w hw v
  have hv : (v.val:ℤ)+1 ≤ 2*p := by exact_mod_cast v.isLt
  have hl : (1:ℤ) ≤ v.val+1 := by omega
  have hp : 0 ≤ scale h := by have := scale_positive h; omega
  have h₁ := mul_le_mul_of_nonneg_right hv hp
  have h₂ := mul_le_mul_of_nonneg_right hl hp
  constructor <;> nlinarith

 theorem ordinaryMiddle_bounds {n : ℕ} (δ lo hi : ℤ) (hδ : 0 ≤ δ) (a : Profile n)
    (ha : ∀ v, lo ≤ a v ∧ a v ≤ hi) (v : Fin n) :
    lo ≤ ordinaryMiddle δ a v ∧ ordinaryMiddle δ a v ≤ hi+δ/2 := by
  unfold ordinaryMiddle
  split_ifs with h
  · have hu := ha v
    have hv := ha ⟨v.val+1,h⟩
    omega
  · have hh := ha v
    omega

 theorem middleProfile_bounds {p : ℕ} (δ lo hi : ℤ) (hδ : 0 ≤ δ) (a : Profile (2*p))
    (ha : ∀ v, lo ≤ a v ∧ a v ≤ hi) (P : CutPair p) (v : Fin (2*p)) :
    lo-1 ≤ middleProfile δ a P v ∧ middleProfile δ a P v ≤ hi+δ/2+1 := by
  have ho := ordinaryMiddle_bounds δ lo hi hδ a ha v
  cases P with
  | background => simp only [middleProfile]; omega
  | leftRise i => have hh := ha (nextTrack i); simp only [middleProfile]; split_ifs  <;>  omega
  | leftDrop i => have hh := ha (firstTrack i); simp only [middleProfile]; split_ifs  <;>  omega
  | rightRise i => have hh := ha (nextTrack i); simp only [middleProfile]; split_ifs  <;>  omega
  | rightDrop i => have hh := ha (firstTrack i); simp only [middleProfile]; split_ifs  <;>  omega

 theorem inputProfile_inside {p h : ℕ} (w : List (CutPair p)) (hw : w.length ≤ h)
    (v : Fin (2*p)) : 0 < inputProfile h w v ∧ inputProfile h w v < commonLength (2*p) h := by
  have hh := inputProfile_bounds w hw v
  unfold commonLength scale at *
  push_cast at *
  constructor  <;>  nlinarith

 theorem middleProfile_inside {p h : ℕ} (w : List (CutPair p)) (hw : w.length ≤ h)
    (P : CutPair p) (v : Fin (2*p)) :
    0 < middleProfile (scale h) (inputProfile h w) P v ∧
      middleProfile (scale h) (inputProfile h w) P v < commonLength (2*p) h := by
  have hh := middleProfile_bounds (scale h) (scale h-2*h) ((2*p)*scale h+2*h)
    (show 0 ≤ scale h by have := scale_positive h; omega) (inputProfile h w)
    (inputProfile_bounds w hw) P v
  have hd : scale h/2 ≤ scale h := by have := scale_positive h; omega
  unfold commonLength scale at *
  push_cast at *
  constructor  <;>  nlinarith

 theorem runOutput_append {p : ℕ} (a : Profile (2*p)) (w z : List (CutPair p)) :
    runOutput a (w++z)=runOutput (runOutput a w) z := by
  induction w generalizing a with
  | nil => rfl
  | cons P w ih => exact ih (outputProfile a P)

@[simp] theorem inputProfile_append_singleton {p h : ℕ} (w : List (CutPair p)) (P : CutPair p) :
    inputProfile h (w++[P])=outputProfile (inputProfile h w) P := by
  unfold inputProfile
  rw [runOutput_append]
  rfl

end HiddenCircuits.GraphReduction.UnitInterval
