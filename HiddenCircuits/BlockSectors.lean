import HiddenCircuits.GlobalFilter

namespace HiddenCircuits
open scoped BigOperators
namespace State
variable {a b u v q : ℕ}

/-- Prefixes ending inside the right block split into all left particles and the right prefix. -/
theorem prefix_join_add (S : State a u) (T : State b v) (c : ℕ) :
    (join S T).prefixCount (a+c) = u + T.prefixCount c := by
  unfold prefixCount join
  rw [Finset.sum_map]
  change (∑ j : Fin u ⊕ Fin v, if (joinTracks S T j).val < a+c then 1 else 0) = _
  rw [Fintype.sum_sum_type]
  have hl : (∑ j : Fin u, if (joinTracks S T (Sum.inl j)).val < a+c then 1 else 0) = u := by
    have h : ∀ j : Fin u, (joinTracks S T (Sum.inl j)).val < a+c := by
      intro j
      have hj := (S.track j).isLt
      simp only [joinTracks_left,Fin.val_castAdd]
      omega
    simp only [if_pos (h _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  rw [hl]
  congr 1
  change _ = T.prefixCount c
  rw [T.prefix_tracks]
  simp only [joinTracks_right,Fin.val_natAdd,Nat.add_lt_add_iff_left]

theorem prefix_le_card (S : State a q) (c : ℕ) : S.prefixCount c ≤ q := by
  rw [prefix_card]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq S.property

/-- Every actual state splits at the cut, retaining precisely the counted particle numbers. -/
theorem exists_join_of_sum (S : State (a+b) q) :
    ∃ (u v : ℕ) (h : q=u+v) (L : State a u) (R : State b v),
      castParticles h S = join L R := by
  let u := S.prefixCount a
  let v := q-u
  have hu : u≤q := S.prefix_le_card a
  have h : q=u+v := by omega
  have hs : (castParticles h S).prefixCount a=u := rfl
  obtain ⟨L,R,he⟩ := exists_join (castParticles h S) hs
  exact ⟨u,v,h,L,R,he.symm⟩
end State

@[simp] theorem globalFilter_castParticles {k q r : ℕ} (h : q=r)
    (S T : State (blockWidth k) q) :
    globalFilter k r (State.castParticles h S) (State.castParticles h T) = globalFilter k q S T := by
  subst r
  rfl

/-- States have the same block counts exactly when their boundary prefixes agree. -/
def SameBlockCounts {k q : ℕ} (S T : State (blockWidth k) q) : Prop :=
  ∀ j : ℕ, j≤k → S.prefixCount (4*j) = T.prefixCount (4*j)

/-- Uniform half filling in every four-track block, expressed on actual selected tracks. -/
def Balanced {k : ℕ} (S : State (blockWidth k) (2*k)) : Prop :=
  ∀ j : ℕ, j≤k → S.prefixCount (4*j) = 2*j

/-- Every nonzero diagonal-count transition has at least two particles in every block.
The aggregate inequality is proved from the actual zero/one filter sectors. -/
theorem globalFilter_sameCounts_minimum (k q : ℕ) (S T : State (blockWidth k) q)
    (he : SameBlockCounts S T) (h : globalFilter k q S T ≠ 0) : 2*k ≤ q := by
  induction k generalizing q with
  | zero => omega
  | succ k ih =>
    obtain ⟨u,v,hq,L,R,hS⟩ := State.exists_join_of_sum (a:=4) (b:=blockWidth k) S
    have he1 : (State.castParticles hq T).prefixCount 4 = u := by
      have hs := congrArg (fun X => X.prefixCount 4) hS
      dsimp only at hs
      rw [State.prefix_join] at hs
      exact (he 1 (by omega)).symm.trans hs
    obtain ⟨L',R',hT⟩ := State.exists_join (State.castParticles hq T) he1
    have hn : localFilter u L L' * globalFilter k v R R' ≠ 0 := by
      have hf := congrFun (congrFun (blockRestrict_globalFilter k u v) (L,R)) (L',R')
      change globalFilter (k+1) (u+v) (State.join L R) (State.join L' R') = _ at hf
      rw [← hS,hT,globalFilter_castParticles] at hf
      rw [hf] at h
      exact h
    have hlu : 2≤u := by
      by_contra hh
      have hc : u=0 ∨ u=1 := by omega
      rcases hc with rfl | rfl <;> simp [localFilter_zero,localFilter_one] at hn
    have her : SameBlockCounts R R' := by
      intro j hj
      have hp := he (j+1) (by omega)
      have hs := congrArg (fun X => X.prefixCount (4*(j+1))) hS
      have ht := congrArg (fun X => X.prefixCount (4*(j+1))) hT
      dsimp only at hs ht
      change S.prefixCount _ = (State.join L R).prefixCount _ at hs
      change (State.join L' R').prefixCount _ = T.prefixCount _ at ht
      rw [show 4*(j+1)=4+4*j by omega,State.prefix_join_add] at hs ht
      rw [show 4*(j+1)=4+4*j by omega] at hp
      omega
    have hv := ih v R R' her (fun hz => hn (by rw [hz,mul_zero]))
    omega


/-- Half filling forces the sole surviving diagonal-count sector to be the balanced one. -/
theorem globalFilter_sameCounts_balanced (k : ℕ) (S T : State (blockWidth k) (2*k))
    (he : SameBlockCounts S T) (h : globalFilter k (2*k) S T ≠ 0) : Balanced S ∧ Balanced T := by
  induction k with
  | zero =>
    constructor <;> intro j hj <;> have : j=0 := by omega
    all_goals subst j; simp [State.prefixCount]
  | succ k ih =>
    obtain ⟨u,v,hq,L,R,hS⟩ := State.exists_join_of_sum (a:=4) (b:=blockWidth k) S
    have he1 : (State.castParticles hq T).prefixCount 4 = u := by
      have hs := congrArg (fun X => X.prefixCount 4) hS
      dsimp only at hs
      rw [State.prefix_join] at hs
      exact (he 1 (by omega)).symm.trans hs
    obtain ⟨L',R',hT⟩ := State.exists_join (State.castParticles hq T) he1
    have hn : localFilter u L L' * globalFilter k v R R' ≠ 0 := by
      have hf := congrFun (congrFun (blockRestrict_globalFilter k u v) (L,R)) (L',R')
      change globalFilter (k+1) (u+v) (State.join L R) (State.join L' R') = _ at hf
      rw [← hS,hT,globalFilter_castParticles] at hf
      rw [hf] at h
      exact h
    have hlu : 2≤u := by
      by_contra hh
      have hc : u=0 ∨ u=1 := by omega
      rcases hc with rfl | rfl <;> simp [localFilter_zero,localFilter_one] at hn
    have her : SameBlockCounts R R' := by
      intro j hj
      have hp := he (j+1) (by omega)
      have hs := congrArg (fun X => X.prefixCount (4*(j+1))) hS
      have ht := congrArg (fun X => X.prefixCount (4*(j+1))) hT
      dsimp only at hs ht
      change S.prefixCount _ = (State.join L R).prefixCount _ at hs
      change (State.join L' R').prefixCount _ = T.prefixCount _ at ht
      rw [show 4*(j+1)=4+4*j by omega,State.prefix_join_add] at hs ht
      rw [show 4*(j+1)=4+4*j by omega] at hp
      omega
    have hv := globalFilter_sameCounts_minimum k v R R' her (fun hz => hn (by rw [hz,mul_zero]))
    have hu : u=2 := by omega
    have hv' : v=2*k := by omega
    subst u
    subst v
    have hbr := ih R R' her (fun hz => hn (by rw [hz,mul_zero]))
    constructor
    · intro j hj
      cases j with
      | zero => simp [State.prefixCount]
      | succ j =>
        have hr := hbr.1 j (by omega)
        have hs := congrArg (fun X => X.prefixCount (4*(j+1))) hS
        dsimp only at hs
        change S.prefixCount _ = (State.join L R).prefixCount _ at hs
        rw [show 4*(j+1)=4+4*j by omega,State.prefix_join_add,hr] at hs
        simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using hs
    · intro j hj
      have hb : S.prefixCount (4*j)=2*j := by
        cases j with
        | zero => simp [State.prefixCount]
        | succ j =>
          have hr := hbr.1 j (by omega)
          have hs := congrArg (fun X => X.prefixCount (4*(j+1))) hS
          dsimp only at hs
          change S.prefixCount _ = (State.join L R).prefixCount _ at hs
          rw [show 4*(j+1)=4+4*j by omega,State.prefix_join_add,hr] at hs
          simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using hs
      exact (he j hj).symm.trans hb

end HiddenCircuits
