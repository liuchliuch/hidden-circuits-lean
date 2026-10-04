import HiddenCircuits.PairedSampling
import HiddenCircuits.GraphReduction.UnitIntervalGeometry

/-! Literal integer profiles from the Section10 geometry table. -/
namespace HiddenCircuits.GraphReduction.UnitInterval

abbrev Profile (n : ℕ) := Fin n → ℤ

def Separated {n : ℕ} (a : Profile n) : Prop :=
  ∀ u v, u.val<v.val → a u+8≤a v

def firstTrack {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val,by omega⟩
def nextTrack {n : ℕ} (i : Fin (n-1)) : Fin n := ⟨i.val+1,by omega⟩

/-- Integer floor midpoint, exactly as in the paper, with its last-track convention. -/
def ordinaryMiddle {n : ℕ} (δ : ℤ) (a : Profile n) (v : Fin n) : ℤ :=
  if h:v.val+1<n then (a v+a ⟨v.val+1,h⟩)/2 else a v+δ/2

/-- Literal four-row middle-profile table. -/
def middleProfile {p : ℕ} (δ : ℤ) (a : Profile (2*p)) (P : CutPair p) (v : Fin (2*p)) : ℤ :=
  match P with
  | .background => ordinaryMiddle δ a v
  | .leftRise i => if v.val=i.val then a (nextTrack i)+1 else ordinaryMiddle δ a v
  | .leftDrop i => if v.val=i.val then a (firstTrack i)-1 else ordinaryMiddle δ a v
  | .rightRise i => if v.val=i.val then a (nextTrack i)-1 else ordinaryMiddle δ a v
  | .rightDrop i => if v.val=i.val then a (firstTrack i)+1 else ordinaryMiddle δ a v

/-- Literal four-row output-profile table; each step changes at most one offset by two. -/
def outputProfile {p : ℕ} (a : Profile (2*p)) (P : CutPair p) (v : Fin (2*p)) : ℤ :=
  match P with
  | .background => a v
  | .leftRise i => if v.val=i.val+1 then a v+2 else a v
  | .leftDrop i => if v.val=i.val then a v-2 else a v
  | .rightRise i => if v.val=i.val+1 then a v-2 else a v
  | .rightDrop i => if v.val=i.val then a v+2 else a v

 theorem ordinaryMiddle_lower {n : ℕ} (δ : ℤ) (a : Profile n) (ha : Separated a)
    (hδ : 8≤δ) (v : Fin n) : a v+2<ordinaryMiddle δ a v := by
  unfold ordinaryMiddle
  split_ifs with h
  · have hh := ha v ⟨v.val+1,h⟩ (by simp)
    omega
  · omega

 theorem ordinaryMiddle_upper {n : ℕ} (δ : ℤ) (a : Profile n) (ha : Separated a)
    (u v : Fin n) (h : v.val<u.val) : ordinaryMiddle δ a v+2<a u := by
  have hv : v.val+1<n := by omega
  rw [ordinaryMiddle,dif_pos hv]
  have hh := ha v ⟨v.val+1,hv⟩ (by simp)
  by_cases he : v.val+1=u.val
  · have he' : (⟨v.val+1,hv⟩ : Fin n)=u := Fin.ext he
    rw [he']
    rw [he'] at hh
    omega
  · have hh' := ha ⟨v.val+1,hv⟩ u (by simp; omega)
    omega

 theorem profile_le {n : ℕ} (a : Profile n) (ha : Separated a) {u v : Fin n}
    (h : u.val≤v.val) : a u≤a v := by
  by_cases he:u=v
  · simp [he]
  · have hne : u.val≠v.val := fun h => he (Fin.ext h)
    have hh := ha u v (by omega)
    omega

 theorem ordinaryMiddle_le_cmp {n : ℕ} (δ : ℤ) (a : Profile n) (ha : Separated a)
    (hδ : 8≤δ) (u v : Fin n) (k : ℤ) (hk : -2≤k ∧ k≤2) :
    a v+k≤ordinaryMiddle δ a u ↔ v.val≤u.val := by
  constructor
  · intro h
    by_contra hv
    have hh := ordinaryMiddle_upper δ a ha v u (by omega)
    omega
  · intro h
    have hh := profile_le a ha h
    have hl := ordinaryMiddle_lower δ a ha hδ u
    omega

 theorem ordinaryMiddle_ge_cmp {n : ℕ} (δ : ℤ) (a : Profile n) (ha : Separated a)
    (hδ : 8≤δ) (u v : Fin n) :
    ordinaryMiddle δ a v≤a u ↔ v.val<u.val := by
  constructor
  · intro h
    by_contra hv
    have hh := profile_le a ha (show u.val≤v.val by omega)
    have hl := ordinaryMiddle_lower δ a ha hδ v
    omega
  · intro h
    have hh := ordinaryMiddle_upper δ a ha u v h
    omega

 theorem profile_shift_cmp {n : ℕ} (a : Profile n) (ha : Separated a)
    (u v : Fin n) (b c : ℤ) (hb : -2≤b ∧ b≤2) (hc : -2≤c ∧ c≤2) :
    a u+b≤a v+c ↔ u.val<v.val ∨ (u.val=v.val ∧ b≤c) := by
  rcases lt_trichotomy u.val v.val with h|h|h
  · have hh := ha u v h
    omega
  · have he : u=v := Fin.ext h
    subst v
    simp
  · have hh := ha v u h
    omega

/-- The first literal interval cut is the entrywise complement of the required first matrix. -/
theorem first_profile_cut {p : ℕ} (δ : ℤ) (a : Profile (2*p)) (ha : Separated a)
    (hδ : 8≤δ) (P : CutPair p) (u v : Fin (2*p)) :
    middleProfile δ a P v≤a u ↔ P.first u v=0 := by
  have ho := ordinaryMiddle_ge_cmp δ a ha hδ u v
  cases P with
  | background =>
    change ordinaryMiddle δ a v≤a u ↔ (if u≤v then (1:ℚ) else 0)=0
    rw [ho]
    split_ifs with h <;> norm_num <;> simp only [Fin.le_def] at h <;> omega
  | leftRise i =>
    have hs := profile_shift_cmp a ha (nextTrack i) u 1 0 (by omega) (by omega)
    simp only [add_zero,← sub_eq_add_neg] at hs
    change (a (nextTrack i)+1≤a u ↔ i.val+1<u.val ∨ (i.val+1=u.val ∧ (1:ℤ)≤0)) at hs
    simp only [middleProfile,CutPair.first,addedCut,upper]
    split_ifs <;> norm_num at *
    all_goals simp only [Fin.lt_def,Fin.le_def] at *
    all_goals omega
  | leftDrop i =>
    have hs := profile_shift_cmp a ha (firstTrack i) u (-1) 0 (by omega) (by omega)
    simp only [add_zero,← sub_eq_add_neg] at hs
    change (a (firstTrack i)-1≤a u ↔ i.val<u.val ∨ (i.val=u.val ∧ (-1:ℤ)≤0)) at hs
    simp only [middleProfile,CutPair.first,deletedCut,upper]
    split_ifs <;> norm_num at *
    all_goals simp only [Fin.lt_def,Fin.le_def] at *
    all_goals omega
  | rightRise i =>
    have hs := profile_shift_cmp a ha (nextTrack i) u (-1) 0 (by omega) (by omega)
    simp only [add_zero,← sub_eq_add_neg] at hs
    change (a (nextTrack i)-1≤a u ↔ i.val+1<u.val ∨ (i.val+1=u.val ∧ (-1:ℤ)≤0)) at hs
    simp only [middleProfile,CutPair.first,upper]
    split_ifs <;> norm_num at *
    all_goals simp only [Fin.lt_def,Fin.le_def] at *
    all_goals omega
  | rightDrop i =>
    have hs := profile_shift_cmp a ha (firstTrack i) u 1 0 (by omega) (by omega)
    simp only [add_zero,← sub_eq_add_neg] at hs
    change (a (firstTrack i)+1≤a u ↔ i.val<u.val ∨ (i.val=u.val ∧ (1:ℤ)≤0)) at hs
    simp only [middleProfile,CutPair.first,upper]
    split_ifs <;> norm_num at *
    all_goals simp only [Fin.lt_def,Fin.le_def] at *
    all_goals omega

/-- The second literal interval cut is exactly the required lower cut. -/
theorem second_profile_cut {p : ℕ} (δ : ℤ) (a : Profile (2*p)) (ha : Separated a)
    (hδ : 8≤δ) (P : CutPair p) (u v : Fin (2*p)) :
    outputProfile a P v≤middleProfile δ a P u ↔ P.second u v=1 := by
  have ho0 := ordinaryMiddle_le_cmp δ a ha hδ u v 0 (by omega)
  have hoP := ordinaryMiddle_le_cmp δ a ha hδ u v 2 (by omega)
  have hoN := ordinaryMiddle_le_cmp δ a ha hδ u v (-2) (by omega)
  cases P with
  | background =>
    change a v≤ordinaryMiddle δ a u ↔ (if v≤u then (1:ℚ) else 0)=1
    simp only [add_zero] at ho0
    rw [ho0]
    split_ifs with h <;> norm_num <;> simp only [Fin.le_def] at h <;> omega
  | leftRise i =>
    have hs0 := profile_shift_cmp a ha v (nextTrack i) 0 1 (by omega) (by omega)
    have hsP := profile_shift_cmp a ha v (nextTrack i) 2 1 (by omega) (by omega)
    have hsN := profile_shift_cmp a ha v (nextTrack i) (-2) 1 (by omega) (by omega)
    simp only [middleProfile,outputProfile,CutPair.second,Matrix.transpose_apply,addedCut,deletedCut,upper]
    dsimp only [nextTrack,firstTrack] at *
    split_ifs <;> norm_num at * <;> simp only [Fin.le_def,sub_eq_add_neg] at * <;> omega
  | leftDrop i =>
    have hs0 := profile_shift_cmp a ha v (firstTrack i) 0 (-1) (by omega) (by omega)
    have hsP := profile_shift_cmp a ha v (firstTrack i) 2 (-1) (by omega) (by omega)
    have hsN := profile_shift_cmp a ha v (firstTrack i) (-2) (-1) (by omega) (by omega)
    simp only [middleProfile,outputProfile,CutPair.second,Matrix.transpose_apply,addedCut,deletedCut,upper]
    dsimp only [nextTrack,firstTrack] at *
    split_ifs <;> norm_num at * <;> simp only [Fin.le_def,sub_eq_add_neg] at * <;> omega
  | rightRise i =>
    have hs0 := profile_shift_cmp a ha v (nextTrack i) 0 (-1) (by omega) (by omega)
    have hsP := profile_shift_cmp a ha v (nextTrack i) 2 (-1) (by omega) (by omega)
    have hsN := profile_shift_cmp a ha v (nextTrack i) (-2) (-1) (by omega) (by omega)
    simp only [middleProfile,outputProfile,CutPair.second,Matrix.transpose_apply,addedCut,deletedCut,upper]
    dsimp only [nextTrack,firstTrack] at *
    split_ifs <;> norm_num at * <;> simp only [Fin.le_def,sub_eq_add_neg] at * <;> omega
  | rightDrop i =>
    have hs0 := profile_shift_cmp a ha v (firstTrack i) 0 1 (by omega) (by omega)
    have hsP := profile_shift_cmp a ha v (firstTrack i) 2 1 (by omega) (by omega)
    have hsN := profile_shift_cmp a ha v (firstTrack i) (-2) 1 (by omega) (by omega)
    simp only [middleProfile,outputProfile,CutPair.second,Matrix.transpose_apply,addedCut,deletedCut,upper]
    dsimp only [nextTrack,firstTrack] at *
    split_ifs <;> norm_num at * <;> simp only [Fin.le_def,sub_eq_add_neg] at * <;> omega

end HiddenCircuits.GraphReduction.UnitInterval
