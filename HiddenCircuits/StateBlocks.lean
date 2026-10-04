import HiddenCircuits.PermanentBlocks
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Equiv.Fin.Basic

namespace HiddenCircuits
namespace State
variable {a b u v : ℕ}

/-- Actual ordered-track inclusion of two disjoint selected blocks. -/
def joinTracks (S : State a u) (T : State b v) : Fin u ⊕ Fin v ↪ Fin (a+b) :=
  (S.track.toEmbedding.sumMap T.track.toEmbedding).trans finSumFinEquiv.toEmbedding

@[simp] theorem joinTracks_left (S : State a u) (T : State b v) (i : Fin u) :
    joinTracks S T (Sum.inl i) = Fin.castAdd b (S.track i) := rfl
@[simp] theorem joinTracks_right (S : State a u) (T : State b v) (i : Fin v) :
    joinTracks S T (Sum.inr i) = Fin.natAdd a (T.track i) := rfl

/-- Concatenation is the concrete union of the selected tracks, not a tensor-space assumption. -/
def join (S : State a u) (T : State b v) : State (a+b) (u+v) :=
  ⟨Finset.univ.map (joinTracks S T), by simp⟩

 theorem joinTracks_mem (S : State a u) (T : State b v) (i : Fin u ⊕ Fin v) :
    joinTracks S T i ∈ (join S T).val :=
  Finset.mem_map.mpr ⟨i,Finset.mem_univ i,rfl⟩

noncomputable def joinElements (S : State a u) (T : State b v) :
    Fin u ⊕ Fin v ≃ (join S T).val :=
  Equiv.ofBijective (fun i => ⟨joinTracks S T i,joinTracks_mem S T i⟩) (by
    constructor
    · intro i j h
      exact (joinTracks S T).injective (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hx
      exact ⟨i,Subtype.ext hi⟩)

noncomputable def joinOrder (S : State a u) (T : State b v) :
    Fin u ⊕ Fin v ≃ Fin (u+v) :=
  (joinElements S T).trans ((join S T).val.orderIsoOfFin (join S T).property).toEquiv.symm

@[simp] theorem joinOrder_track (S : State a u) (T : State b v) (i : Fin u ⊕ Fin v) :
    (join S T).track (joinOrder S T i) = joinTracks S T i := by
  change (((join S T).val.orderIsoOfFin (join S T).property)
    (((join S T).val.orderIsoOfFin (join S T).property).symm (joinElements S T i))).val = _
  simp [joinElements]

end State

/-- Selected permanents can be indexed by the actual selected vertices in the two blocks. -/
theorem compound_join {a b u v : ℕ} (M : Matrix (Fin (a+b)) (Fin (a+b)) ℚ)
    (S₀ T₀ : State a u) (S₁ T₁ : State b v) :
    compound M (State.join S₀ S₁) (State.join T₀ T₁) =
      (M.submatrix (State.joinTracks S₀ S₁) (State.joinTracks T₀ T₁)).permanent := by
  let A := M.submatrix (State.join S₀ S₁).track (State.join T₀ T₁).track
  calc
    compound M (State.join S₀ S₁) (State.join T₀ T₁) =
      (A.submatrix (State.joinOrder S₀ S₁) (State.joinOrder T₀ T₁)).permanent :=
        (permanent_submatrix_two_equiv A _ _).symm
    _ = _ := by
      congr 1
      ext i j
      simp [A]

/-- The diagonal fixed-particle block of a block-upper-triangular permanental compound
is the tensor product of the two actual local compounds. -/
theorem compound_join_upper {a b u v : ℕ} (M : Matrix (Fin (a+b)) (Fin (a+b)) ℚ)
    (hM : ∀ x : Fin b, ∀ y : Fin a, M (Fin.natAdd a x) (Fin.castAdd b y) = 0)
    (S₀ T₀ : State a u) (S₁ T₁ : State b v) :
    compound M (State.join S₀ S₁) (State.join T₀ T₁) =
      compound (M.submatrix (Fin.castAdd b) (Fin.castAdd b)) S₀ T₀ *
      compound (M.submatrix (Fin.natAdd a) (Fin.natAdd a)) S₁ T₁ := by
  rw [compound_join]
  have h := permanent_block_upper (M.submatrix (State.joinTracks S₀ S₁) (State.joinTracks T₀ T₁))
    (fun x y => by simpa using hM (S₁.track x) (T₀.track y))
  simpa [compound,Matrix.submatrix_submatrix,Function.comp_def] using h

end HiddenCircuits
