import HiddenCircuits.StateBlocks
import HiddenCircuits.FlowSupport
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace HiddenCircuits
open scoped BigOperators
namespace State
variable {a b u v q : ℕ}

/-- Splitting the actual selected tracks at a consecutive boundary. -/
def splitTracks (S : State (a+b) q) : Finset (Fin a ⊕ Fin b) :=
  S.val.map finSumFinEquiv.symm.toEmbedding

@[simp] theorem mem_splitTracks_left (S : State (a+b) q) (x : Fin a) :
    Sum.inl x ∈ S.splitTracks ↔ Fin.castAdd b x ∈ S.val := by
  simp [splitTracks]

@[simp] theorem mem_splitTracks_right (S : State (a+b) q) (x : Fin b) :
    Sum.inr x ∈ S.splitTracks ↔ Fin.natAdd a x ∈ S.val := by
  simp [splitTracks]

@[simp] theorem join_mem_left (S : State a u) (T : State b v) (x : Fin a) :
    Fin.castAdd b x ∈ (join S T).val ↔ x ∈ S.val := by
  constructor
  · intro h
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp h
    cases i with
    | inl i =>
      have hx : S.track i = x := Fin.ext (by simpa using congrArg (fun z : Fin (a+b) => z.val) hi)
      rw [← hx, ← S.image_track]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    | inr i =>
      have hv := congrArg Fin.val hi
      simp only [joinTracks_right,Fin.val_natAdd,Fin.val_castAdd] at hv
      have hx := x.isLt
      omega
  · intro hx
    rw [← S.image_track] at hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact joinTracks_mem S T (.inl i)

@[simp] theorem join_mem_right (S : State a u) (T : State b v) (x : Fin b) :
    Fin.natAdd a x ∈ (join S T).val ↔ x ∈ T.val := by
  constructor
  · intro h
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp h
    cases i with
    | inl i =>
      have hv := congrArg Fin.val hi
      simp only [joinTracks_left,Fin.val_natAdd,Fin.val_castAdd] at hv
      have hx := (S.track i).isLt
      omega
    | inr i =>
      have hx : T.track i = x := Fin.ext (by have hh := congrArg Fin.val hi; simp only [joinTracks_right,Fin.val_natAdd] at hh; omega)
      rw [← hx, ← T.image_track]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · intro hx
    rw [← T.image_track] at hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact joinTracks_mem S T (.inr i)

@[simp] theorem splitTracks_join (S : State a u) (T : State b v) :
    (join S T).splitTracks = S.val.disjSum T.val := by
  ext (x | x) <;> simp

theorem prefix_eq_card_left (S : State (a+b) q) :
    S.prefixCount a = S.splitTracks.toLeft.card := by
  rw [prefix_card]
  symm
  apply Finset.card_bij (fun x _ => Fin.castAdd b x)
  · intro x hx
    simp only [Finset.mem_filter]
    exact ⟨mem_splitTracks_left S x |>.mp (Finset.mem_toLeft.mp hx),x.isLt⟩
  · intro x _ y _ h
    exact Fin.ext (by simpa using congrArg (fun z : Fin (a+b) => z.val) h)
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    let x : Fin a := ⟨y.val,hy'.2⟩
    have he : Fin.castAdd b x = y := Fin.ext rfl
    refine ⟨x,?_,he⟩
    simpa only [Finset.mem_toLeft,mem_splitTracks_left,he] using hy'.1

@[simp] theorem prefix_join (S : State a u) (T : State b v) :
    (join S T).prefixCount a = u := by
  simp [prefix_eq_card_left,S.property]

/-- The fixed-particle sector at one cut consists exactly of pairs of local subset states. -/
theorem exists_join (S : State (a+b) (u+v)) (h : S.prefixCount a = u) :
    ∃ L : State a u, ∃ R : State b v, join L R = S := by
  have hl : S.splitTracks.toLeft.card = u := by rwa [prefix_eq_card_left] at h
  have hr : S.splitTracks.toRight.card = v := by
    have hh := Finset.card_toLeft_add_card_toRight (u:=S.splitTracks)
    have hs : S.splitTracks.card = u+v := by simp [splitTracks,S.property]
    omega
  let L : State a u := ⟨S.splitTracks.toLeft,hl⟩
  let R : State b v := ⟨S.splitTracks.toRight,hr⟩
  refine ⟨L,R,?_⟩
  apply Subtype.ext
  ext x
  obtain ⟨y,rfl⟩ := finSumFinEquiv.surjective x
  cases y with
  | inl y => simp [L]
  | inr y => simp [R]

theorem join_injective : Function.Injective (fun p : State a u × State b v => join p.1 p.2) := by
  rintro ⟨L,R⟩ ⟨L',R'⟩ h
  have hs := congrArg splitTracks h
  rw [splitTracks_join,splitTracks_join] at hs
  have hl := congrArg Finset.toLeft hs
  have hr := congrArg Finset.toRight hs
  exact Prod.ext (Subtype.ext (by simpa using hl)) (Subtype.ext (by simpa using hr))

end State

/-- Restriction to actual selected-track states with prescribed counts on both sides. -/
def blockRestrict {a b u v : ℕ} (M : Matrix (State (a+b) (u+v)) (State (a+b) (u+v)) ℚ) :
    Matrix (State a u × State b v) (State a u × State b v) ℚ :=
  M.submatrix (fun S => State.join S.1 S.2) (fun T => State.join T.1 T.2)

@[simp] theorem blockRestrict_one (a b u v : ℕ) :
    blockRestrict (1 : Matrix (State (a+b) (u+v)) (State (a+b) (u+v)) ℚ) = 1 := by
  ext S T
  simp [blockRestrict,Matrix.one_apply,State.join_injective.eq_iff]

/-- No compensating return across the cut is possible in a product. -/
theorem blockRestrict_mul {a b u v : ℕ}
    (A B : Matrix (State (a+b) (u+v)) (State (a+b) (u+v)) ℚ)
    (hA : ∀ S T, A S T ≠ 0 → T.prefixCount a ≤ S.prefixCount a)
    (hB : ∀ S T, B S T ≠ 0 → T.prefixCount a ≤ S.prefixCount a) :
    blockRestrict (A*B) = blockRestrict A * blockRestrict B := by
  classical
  ext S T
  let f : State a u × State b v → State (a+b) (u+v) := fun K => State.join K.1 K.2
  change (∑ K, A (f S) K * B K (f T)) = ∑ K, A (f S) (f K) * B (f K) (f T)
  have hz : ∀ K ∈ Finset.univ, K ∉ Finset.univ.image f → A (f S) K * B K (f T) = 0 := by
    intro K _ hout
    by_contra hn
    have ha : A (f S) K ≠ 0 := fun h => hn (by rw [h,zero_mul])
    have hb : B K (f T) ≠ 0 := fun h => hn (by rw [h,mul_zero])
    have h1 := hA (f S) K ha
    have h2 := hB K (f T) hb
    simp only [f,State.prefix_join] at h1 h2
    obtain ⟨L,R,he⟩ := State.exists_join K (by omega)
    exact hout (Finset.mem_image.mpr ⟨(L,R),Finset.mem_univ _,he⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) hz]
  exact Finset.sum_image State.join_injective.injOn

open scoped Kronecker

/-- The diagonal compound block is an actual tensor product. -/
theorem blockRestrict_compound {a b u v : ℕ} (M : Matrix (Fin (a+b)) (Fin (a+b)) ℚ)
    (hM : ∀ x : Fin b, ∀ y : Fin a, M (Fin.natAdd a x) (Fin.castAdd b y) = 0) :
    blockRestrict (compound (q:=u+v) M) =
      compound (q:=u) (M.submatrix (Fin.castAdd b) (Fin.castAdd b)) ⊗ₖ
      compound (q:=v) (M.submatrix (Fin.natAdd a) (Fin.natAdd a)) := by
  ext S T
  exact compound_join_upper M hM S.1 T.1 S.2 T.2

@[simp] theorem blockRestrict_upper (a b u v : ℕ) :
    blockRestrict (compound (q:=u+v) (upper (a+b))) =
      compound (q:=u) (upper a) ⊗ₖ compound (q:=v) (upper b) := by
  rw [blockRestrict_compound _ (by
    intro x y
    have hy := y.isLt
    simp only [upper,Fin.le_def,Fin.val_natAdd,Fin.val_castAdd]
    rw [if_neg (by omega)])]
  have hl : (upper (a+b)).submatrix (Fin.castAdd b) (Fin.castAdd b) = upper a := by
    ext x y; simp only [Matrix.submatrix_apply, upper,Fin.le_def,Fin.val_castAdd,Fin.val_natAdd,Nat.add_le_add_iff_left]
  have hr : (upper (a+b)).submatrix (Fin.natAdd a) (Fin.natAdd a) = upper b := by
    ext x y; simp only [Matrix.submatrix_apply, upper,Fin.le_def,Fin.val_castAdd,Fin.val_natAdd,Nat.add_le_add_iff_left]
  rw [hl,hr]

/-- Restricting the genuine global inverse gives the tensor product of genuine local inverses. -/
theorem blockRestrict_upperInverse (a b u v : ℕ) :
    blockRestrict (upperInverse (a+b) (u+v)) =
      upperInverse a u ⊗ₖ upperInverse b v := by
  let I := blockRestrict (upperInverse (a+b) (u+v))
  let F := compound (q:=u) (upper a) ⊗ₖ compound (q:=v) (upper b)
  let J := upperInverse a u ⊗ₖ upperInverse b v
  have hi : I*F = 1 := by
    dsimp only [I,F]
    rw [← blockRestrict_upper]
    rw [← blockRestrict_mul _ _
      (fun S T h => upperInverse_prefix_flow (a+b) (u+v) S T h a)
      (fun S T h => upper_prefix_flow (a+b) (u+v) S T h a),upperInverse_mul,blockRestrict_one]
  have hj : F*J=1 := by
    dsimp only [F,J]
    rw [← Matrix.mul_kronecker_mul,mul_upperInverse,mul_upperInverse,Matrix.one_kronecker_one]
  change I=J
  calc
    I = I*(F*J) := by rw [hj,mul_one]
    _ = (I*F)*J := by rw [Matrix.mul_assoc]
    _ = J := by rw [hi,one_mul]

end HiddenCircuits
