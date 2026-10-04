import HiddenCircuits.BlockLetters

namespace HiddenCircuits
open scoped Kronecker
namespace State
variable {n q r a b u v : ℕ}

def castParticles (h : q=r) (S : State n q) : State n r := ⟨S.val,S.property.trans h⟩
@[simp] theorem castParticles_val (h : q=r) (S : State n q) : (castParticles h S).val = S.val := rfl
@[simp] theorem castParticles_self (h : q=q) (S : State n q) : castParticles h S = S := rfl

theorem card_le (S : State n q) : q ≤ n := by
  have h := Finset.card_le_card (Finset.subset_univ S.val)
  simpa [S.property] using h

theorem complement_injective : Function.Injective (complement : State n q → State n (n-q)) := by
  intro S T h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  simpa only [complement_val,compl_inj_iff] using he

theorem complement_join (S : State a u) (T : State b v)
    (h : (a+b)-(u+v)=(a-u)+(b-v)) :
    castParticles h (join S T).complement = join S.complement T.complement := by
  apply Subtype.ext
  ext x
  obtain ⟨y,rfl⟩ := finSumFinEquiv.surjective x
  cases y with
  | inl y => simp
  | inr y => simp
end State

@[simp] theorem rise_castParticles {n q r : ℕ} (h : q=r) (i : Fin (n-1)) (S T : State n q) :
    rise n r i (State.castParticles h S) (State.castParticles h T) = rise n q i S T := by
  subst r
  rfl

@[simp] theorem drop_castParticles {n q r : ℕ} (h : q=r) (i : Fin (n-1)) (S T : State n q) :
    drop n r i (State.castParticles h S) (State.castParticles h T) = drop n q i S T := by
  subst r
  rfl

theorem blockRestrict_dualRise_left (a b u v : ℕ) (i : Fin (a-1)) :
    blockRestrict (dualRise (a+b) (u+v) (leftIndex b i)) =
      dualRise a u i ⊗ₖ (1 : Matrix (State b v) (State b v) ℚ) := by
  ext S T
  have hu := S.1.card_le
  have hv := S.2.card_le
  have hq : (a+b)-(u+v)=(a-u)+(b-v) := by omega
  change rise (a+b) ((a+b)-(u+v)) (leftIndex b i)
    (State.join T.1 T.2).complement (State.join S.1 S.2).complement = _
  rw [← rise_castParticles hq,State.complement_join,State.complement_join]
  have h := congrFun (congrFun (blockRestrict_rise_left a b (a-u) (b-v) i)
    (T.1.complement,T.2.complement)) (S.1.complement,S.2.complement)
  simpa only [blockRestrict,Matrix.submatrix_apply,Matrix.kronecker_apply,Matrix.one_apply,
    State.complement_injective.eq_iff,eq_comm,dualRise] using h

theorem blockRestrict_dualRise_right (a b u v : ℕ) (i : Fin (b-1)) :
    blockRestrict (dualRise (a+b) (u+v) (rightIndex a i)) =
      (1 : Matrix (State a u) (State a u) ℚ) ⊗ₖ dualRise b v i := by
  ext S T
  have hu := S.1.card_le
  have hv := S.2.card_le
  have hq : (a+b)-(u+v)=(a-u)+(b-v) := by omega
  change rise (a+b) ((a+b)-(u+v)) (rightIndex a i)
    (State.join T.1 T.2).complement (State.join S.1 S.2).complement = _
  rw [← rise_castParticles hq,State.complement_join,State.complement_join]
  have h := congrFun (congrFun (blockRestrict_rise_right a b (a-u) (b-v) i)
    (T.1.complement,T.2.complement)) (S.1.complement,S.2.complement)
  simpa only [blockRestrict,Matrix.submatrix_apply,Matrix.kronecker_apply,Matrix.one_apply,
    State.complement_injective.eq_iff,eq_comm,dualRise] using h

theorem blockRestrict_dualDrop_left (a b u v : ℕ) (i : Fin (a-1)) :
    blockRestrict (dualDrop (a+b) (u+v) (leftIndex b i)) =
      dualDrop a u i ⊗ₖ (1 : Matrix (State b v) (State b v) ℚ) := by
  ext S T
  have hu := S.1.card_le
  have hv := S.2.card_le
  have hq : (a+b)-(u+v)=(a-u)+(b-v) := by omega
  change drop (a+b) ((a+b)-(u+v)) (leftIndex b i)
    (State.join T.1 T.2).complement (State.join S.1 S.2).complement = _
  rw [← drop_castParticles hq,State.complement_join,State.complement_join]
  have h := congrFun (congrFun (blockRestrict_drop_left a b (a-u) (b-v) i)
    (T.1.complement,T.2.complement)) (S.1.complement,S.2.complement)
  simpa only [blockRestrict,Matrix.submatrix_apply,Matrix.kronecker_apply,Matrix.one_apply,
    State.complement_injective.eq_iff,eq_comm,dualDrop] using h

theorem blockRestrict_dualDrop_right (a b u v : ℕ) (i : Fin (b-1)) :
    blockRestrict (dualDrop (a+b) (u+v) (rightIndex a i)) =
      (1 : Matrix (State a u) (State a u) ℚ) ⊗ₖ dualDrop b v i := by
  ext S T
  have hu := S.1.card_le
  have hv := S.2.card_le
  have hq : (a+b)-(u+v)=(a-u)+(b-v) := by omega
  change drop (a+b) ((a+b)-(u+v)) (rightIndex a i)
    (State.join T.1 T.2).complement (State.join S.1 S.2).complement = _
  rw [← drop_castParticles hq,State.complement_join,State.complement_join]
  have h := congrFun (congrFun (blockRestrict_drop_right a b (a-u) (b-v) i)
    (T.1.complement,T.2.complement)) (S.1.complement,S.2.complement)
  simpa only [blockRestrict,Matrix.submatrix_apply,Matrix.kronecker_apply,Matrix.one_apply,
    State.complement_injective.eq_iff,eq_comm,dualDrop] using h

end HiddenCircuits
