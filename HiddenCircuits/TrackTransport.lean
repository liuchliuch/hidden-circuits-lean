import HiddenCircuits.BlockWords

namespace HiddenCircuits
namespace State
/-- Relabel a state along an equality of its track count. -/
def castTracks {n m q : ℕ} (h : n=m) (S : State n q) : State m q := h ▸ S
@[simp] theorem castTracks_rfl {n q : ℕ} (S : State n q) : castTracks rfl S = S := rfl
@[simp] theorem castTracks_trans {n m l q : ℕ} (h : n=m) (g : m=l) (S : State n q) :
    castTracks g (castTracks h S) = castTracks (h.trans g) S := by subst m; subst l; rfl
@[simp] theorem castTracks_prefix {n m q : ℕ} (h : n=m) (S : State n q) (c : ℕ) :
    (castTracks h S).prefixCount c = S.prefixCount c := by subst m; rfl
end State
namespace Letter
/-- Relabel a letter along an equality of ambient track counts. -/
def castTracks {n m : ℕ} (h : n=m) (l : Letter n) : Letter m := h ▸ l
@[simp] theorem castTracks_kind {n m : ℕ} (h : n=m) (l : Letter n) :
    (castTracks h l).kind = l.kind := by subst m; rfl
@[simp] theorem castTracks_index {n m : ℕ} (h : n=m) (l : Letter n) :
    (castTracks h l).index.val = l.index.val := by subst m; rfl

theorem eq_of_kind_index {n : ℕ} (l m : Letter n) (hk : l.kind=m.kind)
    (hi : l.index.val=m.index.val) : l=m := by
  cases l with
  | mk lk li =>
    cases m with
    | mk mk mi =>
      simp only [Letter.mk.injEq]
      exact ⟨hk,Fin.ext hi⟩

/-- Shift every letter into an actual containing track interval. -/
def embed {n : ℕ} (N offset : ℕ) (h : offset+n ≤ N) (l : Letter n) : Letter N :=
  ⟨l.kind,⟨offset+l.index.val,by have hh := l.index.isLt; omega⟩⟩

@[simp] theorem embed_inLeft {n b N o : ℕ} (h : o+(n+b) ≤ N) (l : Letter n) :
    embed N o h (l.inLeft b) = embed N o (by omega) l := by
  apply eq_of_kind_index <;> rfl

@[simp] theorem embed_inRight {n a N o : ℕ} (h : o+(a+n) ≤ N) (l : Letter n) :
    embed N o h (l.inRight a) = embed N (o+a) (by omega) l := by
  apply eq_of_kind_index
  · rfl
  · simp only [embed,inRight,rightIndex]
    omega
end Letter

/-- Transport an actual matrix to an equal-sized track space. -/
def matrixCastTracks {n m q : ℕ} (h : n=m)
    (M : Matrix (State n q) (State n q) ℚ) : Matrix (State m q) (State m q) ℚ :=
  M.submatrix (State.castTracks h.symm) (State.castTracks h.symm)

@[simp] theorem matrixCastTracks_mul {n m q : ℕ} (h : n=m)
    (A B : Matrix (State n q) (State n q) ℚ) :
    matrixCastTracks h (A*B) = matrixCastTracks h A * matrixCastTracks h B := by
  subst m
  rfl
@[simp] theorem matrixCastTracks_pow {n m q : ℕ} (h : n=m)
    (A : Matrix (State n q) (State n q) ℚ) (r : ℕ) :
    matrixCastTracks h (A^r) = (matrixCastTracks h A)^r := by subst m; rfl
@[simp] theorem matrixCastTracks_smul {n m q : ℕ} (h : n=m)
    (A : Matrix (State n q) (State n q) ℚ) (r : ℚ) :
    matrixCastTracks h (r • A) = r • matrixCastTracks h A := by subst m; rfl
@[simp] theorem matrixCastTracks_word {n m q : ℕ} (h : n=m) (w : List (Letter n)) :
    matrixCastTracks h (wordMatrix q w) = wordMatrix q (w.map (Letter.castTracks h)) := by
  subst m
  change wordMatrix q w = wordMatrix q (w.map id)
  rw [List.map_id]

end HiddenCircuits
