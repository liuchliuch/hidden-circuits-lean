import HiddenCircuits.BlockSectors

namespace HiddenCircuits
open scoped Kronecker BigOperators

/-- Concrete tuple coordinates in the balanced sector. -/
def BalancedStates : ℕ → Type
  | 0 => PUnit
  | k+1 => State 4 2 × BalancedStates k

instance balancedStatesDecidableEq : (k : ℕ) → DecidableEq (BalancedStates k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k+1 => by
      letI := balancedStatesDecidableEq k
      exact inferInstanceAs (DecidableEq (_ × _))
instance balancedStatesFintype : (k : ℕ) → Fintype (BalancedStates k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k+1 => by
      letI := balancedStatesFintype k
      exact inferInstanceAs (Fintype (_ × _))

/-- The actual selected tracks formed by joining two-particle local states. -/
def balancedJoin : (k : ℕ) → BalancedStates k → State (blockWidth k) (2*k)
  | 0, _ => ⟨∅,rfl⟩
  | k+1, S => State.castParticles (by omega) (State.join S.1 (balancedJoin k S.2))

/-- The balanced diagonal block, as a concrete tensor of actual local filters. -/
def balancedTensor : (k : ℕ) → Matrix (BalancedStates k) (BalancedStates k) ℚ
  | 0 => 1
  | k+1 => localFilter 2 ⊗ₖ balancedTensor k

 theorem balancedJoin_injective (k : ℕ) : Function.Injective (balancedJoin k) := by
  induction k with
  | zero => intro S T _; cases S; cases T; rfl
  | succ k ih =>
    intro S T h
    have hj : State.join S.1 (balancedJoin k S.2) = State.join T.1 (balancedJoin k T.2) := by
      apply Subtype.ext
      exact congrArg (fun X : State (blockWidth (k+1)) (2*(k+1)) => X.val) h
    have hh : (S.1,balancedJoin k S.2) = (T.1,balancedJoin k T.2) :=
      State.join_injective (a:=4) (b:=blockWidth k) (u:=2) (v:=2*k) hj
    change (S.1,S.2) = (T.1,T.2)
    exact Prod.ext (congrArg (fun X : State 4 2 × State (blockWidth k) (2*k) => X.1) hh)
      (ih (congrArg (fun X : State 4 2 × State (blockWidth k) (2*k) => X.2) hh))

 theorem balancedJoin_balanced (k : ℕ) (S : BalancedStates k) : Balanced (balancedJoin k S) := by
  induction k with
  | zero =>
    intro j hj
    have : j=0 := by omega
    subst j
    simp [State.prefixCount]
  | succ k ih =>
    intro j hj
    cases j with
    | zero => simp [State.prefixCount]
    | succ j =>
      change (State.join S.1 (balancedJoin k S.2)).prefixCount (4*(j+1)) = 2*(j+1)
      rw [show 4*(j+1)=4+4*j by omega,State.prefix_join_add,ih S.2 j (by omega)]
      omega

/-- Every balanced actual subset is represented, so no ambient coordinates are omitted. -/
theorem balancedJoin_surjective (k : ℕ) (S : State (blockWidth k) (2*k)) (h : Balanced S) :
    ∃ T, balancedJoin k T = S := by
  induction k with
  | zero =>
    refine ⟨PUnit.unit,?_⟩
    apply Subtype.ext
    exact (Finset.card_eq_zero.mp S.property).symm
  | succ k ih =>
    have hq : 2*(k+1)=2+2*k := by omega
    have hc : (State.castParticles hq S).prefixCount 4=2 := by simpa using h 1 (by omega)
    obtain ⟨L,R,he⟩ := State.exists_join (State.castParticles hq S) hc
    have hr : Balanced R := by
      intro j hj
      have hb := h (j+1) (by omega)
      have hp := congrArg (fun X => X.prefixCount (4*(j+1))) he
      dsimp only at hp
      change (State.join L R).prefixCount _ = S.prefixCount _ at hp
      rw [show 4*(j+1)=4+4*j by omega,State.prefix_join_add] at hp
      rw [show 4*(j+1)=4+4*j by omega] at hb
      omega
    obtain ⟨R',hR⟩ := ih R hr
    refine ⟨(L,R'),?_⟩
    apply Subtype.ext
    change (State.join L (balancedJoin k R')).val = S.val
    rw [hR]
    exact congrArg Subtype.val he

 theorem balancedTensor_eq_restrict (k : ℕ) :
    (globalFilter k (2*k)).submatrix (balancedJoin k) (balancedJoin k) = balancedTensor k := by
  induction k with
  | zero =>
    ext S T
    cases S; cases T
    simp [globalFilter,globalFilterWord,balancedTensor,balancedJoin]
  | succ k ih =>
    ext S T
    change globalFilter (k+1) (2*(k+1)) (balancedJoin (k+1) S) (balancedJoin (k+1) T) = _
    simp only [balancedJoin,globalFilter_castParticles]
    have hh := congrFun (congrFun (blockRestrict_globalFilter k 2 (2*k))
      (S.1,balancedJoin k S.2)) (T.1,balancedJoin k T.2)
    have hi := congrFun (congrFun ih S.2) T.2
    change globalFilter k (2*k) (balancedJoin k S.2) (balancedJoin k T.2) = balancedTensor k S.2 T.2 at hi
    simpa only [blockRestrict,Matrix.submatrix_apply,balancedTensor,Matrix.kroneckerMap_apply,hi] using hh

 theorem balancedTensor_idempotent (k : ℕ) : balancedTensor k * balancedTensor k = balancedTensor k := by
  induction k with
  | zero => simp [balancedTensor]
  | succ k ih =>
    simp only [balancedTensor]
    rw [← Matrix.mul_kronecker_mul,localFilter_idempotent,ih]

end HiddenCircuits
