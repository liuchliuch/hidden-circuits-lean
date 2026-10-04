import HiddenCircuits.GraphReduction.UnitIntervalProfileBounds

/-! A literal list of all emitted layer profiles, with exact indexed transition identities. -/
namespace HiddenCircuits.GraphReduction.UnitInterval

def profileLayers {p : ℕ} (δ : ℤ) (a : Profile (2*p)) :
    List (CutPair p) → List (Profile (2*p))
  | [] => [a]
  | P::w => a :: middleProfile δ a P :: profileLayers δ (outputProfile a P) w

@[simp] theorem profileLayers_length {p : ℕ} (δ : ℤ) (a : Profile (2*p))
    (w : List (CutPair p)) : (profileLayers δ a w).length=2*w.length+1 := by
  induction w generalizing a with
  | nil => rfl
  | cons P w ih => simp [profileLayers,ih]; omega

 theorem profileLayers_even {p : ℕ} (δ : ℤ) (a : Profile (2*p))
    (w : List (CutPair p)) (i : ℕ) (hi : i≤w.length) :
    (profileLayers δ a w)[2*i]'(by rw [profileLayers_length]; omega)=
      runOutput a (w.take i) := by
  induction w generalizing a i with
  | nil =>
    have he : i=0 := by simpa using hi
    subst i
    rfl
  | cons P w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hh := ih (outputProfile a P) i (by simp at hi; omega)
      simpa [profileLayers,Nat.mul_add,Nat.add_assoc,List.take_succ_cons,runOutput] using hh

 theorem profileLayers_odd {p : ℕ} (δ : ℤ) (a : Profile (2*p))
    (w : List (CutPair p)) (i : ℕ) (hi : i<w.length) :
    (profileLayers δ a w)[2*i+1]'(by rw [profileLayers_length]; omega)=
      middleProfile δ (runOutput a (w.take i)) (w[i]) := by
  induction w generalizing a i with
  | nil => simp at hi
  | cons P w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hh := ih (outputProfile a P) i (by simp at hi; omega)
      simpa [profileLayers,Nat.mul_add,Nat.add_assoc,List.take_succ_cons,runOutput] using hh

 theorem runOutput_take_succ {p : ℕ} (a : Profile (2*p)) (w : List (CutPair p))
    (i : ℕ) (hi : i<w.length) :
    runOutput a (w.take (i+1))=outputProfile (runOutput a (w.take i)) w[i] := by
  induction w generalizing a i with
  | nil => simp at hi
  | cons P w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa [List.take_succ_cons,runOutput] using ih (outputProfile a P) i (by simp at hi; omega)

/-- The emitted profile at a concrete layer position. -/
def layerProfile {p : ℕ} (δ : ℤ) (a : Profile (2*p)) (w : List (CutPair p))
    (j : Fin (2*w.length+1)) : Profile (2*p) :=
  (profileLayers δ a w)[j.val]'(by rw [profileLayers_length]; exact j.isLt)

 theorem layerProfile_even {p : ℕ} (δ : ℤ) (a : Profile (2*p))
    (w : List (CutPair p)) (i : ℕ) (hi : i≤w.length) :
    layerProfile δ a w ⟨2*i,by omega⟩=runOutput a (w.take i) :=
  profileLayers_even δ a w i hi

 theorem layerProfile_odd {p : ℕ} (δ : ℤ) (a : Profile (2*p))
    (w : List (CutPair p)) (i : ℕ) (hi : i<w.length) :
    layerProfile δ a w ⟨2*i+1,by omega⟩=
      middleProfile δ (runOutput a (w.take i)) w[i] :=
  profileLayers_odd δ a w i hi


 theorem layerProfile_inside {p h : ℕ} (w : List (CutPair p)) (hw : w.length≤h)
    (j : Fin (2*w.length+1)) (v : Fin (2*p)) :
    0<layerProfile (scale h) (initialProfile (2*p) (scale h)) w j v ∧
      layerProfile (scale h) (initialProfile (2*p) (scale h)) w j v<commonLength (2*p) h := by
  have hj := j.isLt
  have hmod := Nat.mod_lt j.val (by decide : 0<2)
  have hdiv := Nat.mod_add_div j.val 2
  by_cases he : j.val%2=0
  · have hi : j.val/2≤w.length := by omega
    have heq : j=⟨2*(j.val/2),by omega⟩ := Fin.ext (by dsimp; omega)
    have hp := layerProfile_even (scale h) (initialProfile (2*p) (scale h)) w (j.val/2) hi
    rw [←heq] at hp
    rw [hp]
    exact inputProfile_inside (w.take (j.val/2)) (by simp; omega) v
  · have hi : j.val/2<w.length := by omega
    have heq : j=⟨2*(j.val/2)+1,by omega⟩ := Fin.ext (by dsimp; omega)
    have hp := layerProfile_odd (scale h) (initialProfile (2*p) (scale h)) w (j.val/2) hi
    rw [←heq] at hp
    rw [hp]
    exact middleProfile_inside (w.take (j.val/2)) (by simp; omega) w[j.val/2] v

 theorem layerProfile_first_cut {p h : ℕ} (w : List (CutPair p)) (hw : w.length≤h)
    (i : ℕ) (hi : i<w.length) (u v : Fin (2*p)) :
    layerProfile (scale h) (initialProfile (2*p) (scale h)) w ⟨2*i+1,by omega⟩ v ≤
      layerProfile (scale h) (initialProfile (2*p) (scale h)) w ⟨2*i,by omega⟩ u ↔
      w[i].first u v=0 := by
  rw [layerProfile_odd _ _ _ i hi,layerProfile_even _ _ _ i hi.le]
  exact first_profile_cut (scale h) (inputProfile h (w.take i))
    (inputProfile_separated (w.take i) (by simp; omega)) (scale_positive h) w[i] u v

 theorem layerProfile_second_cut {p h : ℕ} (w : List (CutPair p)) (hw : w.length≤h)
    (i : ℕ) (hi : i<w.length) (u v : Fin (2*p)) :
    layerProfile (scale h) (initialProfile (2*p) (scale h)) w ⟨2*(i+1),by omega⟩ v ≤
      layerProfile (scale h) (initialProfile (2*p) (scale h)) w ⟨2*i+1,by omega⟩ u ↔
      w[i].second u v=1 := by
  rw [layerProfile_even _ _ _ (i+1) (by omega),layerProfile_odd _ _ _ i hi,
    runOutput_take_succ _ _ i hi]
  exact second_profile_cut (scale h) (inputProfile h (w.take i))
    (inputProfile_separated (w.take i) (by simp; omega)) (scale_positive h) w[i] u v

end HiddenCircuits.GraphReduction.UnitInterval
