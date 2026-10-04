import HiddenCircuits.GlobalRank

namespace HiddenCircuits
open scoped BigOperators Kronecker

/-- Logical bits, with their literal four-track encodings 1010 and 0110. -/
def localRawCode (i : Fin 2) : State 4 2 := if i=0 then Small.states2 1 else Small.states2 3

 theorem localRawCode_injective : Function.Injective localRawCode := by
  decide +kernel

 theorem localRawCode_fixed (i : Fin 2) (T : State 4 2) :
    localFilter 2 (localRawCode i) T = if T=localRawCode i then 1 else 0 := by
  fin_cases i
  · simpa only [localRawCode,if_pos rfl] using localFilter_fixes_zero T
  · simpa only [localRawCode,show (1:Fin 2)≠0 by decide,if_false] using localFilter_fixes_one T

/-- Logical bit strings, recursively grouped to match consecutive physical blocks. -/
def CodeBits : ℕ → Type
  | 0 => PUnit
  | k+1 => Fin 2 × CodeBits k
instance codeBitsDecidableEq : (k : ℕ) → DecidableEq (CodeBits k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k+1 => by
      letI := codeBitsDecidableEq k
      exact inferInstanceAs (DecidableEq (_ × _))
instance codeBitsFintype : (k : ℕ) → Fintype (CodeBits k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k+1 => by
      letI := codeBitsFintype k
      exact inferInstanceAs (Fintype (_ × _))

@[simp] theorem codeBits_card (k : ℕ) : Fintype.card (CodeBits k) = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Fintype.card (Fin 2 × CodeBits k) = _
    rw [Fintype.card_prod,Fintype.card_fin,ih,pow_succ']

/-- The two distinguished local states in each balanced-sector tuple. -/
def codeTuple : (k : ℕ) → CodeBits k → BalancedStates k
  | 0, _ => PUnit.unit
  | k+1, x => (localRawCode x.1,codeTuple k x.2)

 theorem codeTuple_injective (k : ℕ) : Function.Injective (codeTuple k) := by
  induction k with
  | zero => intro x y _; cases x; cases y; rfl
  | succ k ih =>
    intro x y h
    have hl := congrArg (fun S : BalancedStates (k+1) => S.1) h
    have hr := congrArg (fun S : BalancedStates (k+1) => S.2) h
    change localRawCode x.1 = localRawCode y.1 at hl
    change codeTuple k x.2 = codeTuple k y.2 at hr
    exact Prod.ext (localRawCode_injective hl) (ih hr)

/-- The actual selected-track subset obtained by replacing every bit with its four-track code. -/
def rawCode (k : ℕ) (x : CodeBits k) : State (blockWidth k) (2*k) := balancedJoin k (codeTuple k x)

 theorem rawCode_injective (k : ℕ) : Function.Injective (rawCode k) :=
  (balancedJoin_injective k).comp (codeTuple_injective k)

 theorem rawCode_balanced (k : ℕ) (x : CodeBits k) : Balanced (rawCode k x) :=
  balancedJoin_balanced k _

/-- Every raw code row is fixed by the actual balanced diagonal tensor. -/
theorem codeTuple_fixed (k : ℕ) (x : CodeBits k) (T : BalancedStates k) :
    balancedTensor k (codeTuple k x) T = if T=codeTuple k x then 1 else 0 := by
  induction k with
  | zero =>
    cases x; cases T
    change (1 : Matrix PUnit PUnit ℚ) PUnit.unit PUnit.unit = 1
    simp
  | succ k ih =>
    change localFilter 2 (localRawCode x.1) T.1 * balancedTensor k (codeTuple k x.2) T.2 = _
    rw [localRawCode_fixed,ih x.2 T.2]
    change _ = if (T.1,T.2)=(localRawCode x.1,codeTuple k x.2) then 1 else 0
    simp only [Prod.mk.injEq,ite_mul,mul_ite,one_mul,zero_mul,mul_one,mul_zero]
    split_ifs <;> simp_all [Prod.ext_iff]

/-- Equal-potential entries of every positive filter power retain exactly the balanced block. -/
theorem globalProjection_balanced_entry (k : ℕ) (S T : State (blockWidth k) (2*k))
    (hS : Balanced S) (hT : Balanced T) : globalProjection k S T = globalDiagonal k S T := by
  have hp := potential_pow_equal_level (globalFilter k (2*k)) (globalDiagonal k)
    State.boundaryPotential (fun S T => globalFilter_potential_le S T)
    (fun S T h => (globalDiagonal_potential_eq S T h).le)
    (fun S T => globalFilter_eq_diagonal_of_potential_eq S T)
    (globalProjectionExponent k) S T (balanced_potential_eq S T hS hT)
  have hd : (globalDiagonal k)^(globalProjectionExponent k)=globalDiagonal k := by
    have hs : (globalDiagonal k)^(1+1)=(globalDiagonal k)^1 := by
      simpa only [show (1:ℕ)+1=2 by rfl,pow_two,pow_one] using globalDiagonal_idempotent k
    simpa only [pow_one] using powers_eq_after hs (globalProjectionExponent k)
      (by unfold globalProjectionExponent; omega)
  simpa only [globalProjection,hd] using hp

 theorem globalProjection_rawCode (k : ℕ) (x y : CodeBits k) :
    globalProjection k (rawCode k x) (rawCode k y) = if x=y then 1 else 0 := by
  rw [globalProjection_balanced_entry k _ _ (rawCode_balanced k x) (rawCode_balanced k y)]
  rw [rawCode,rawCode,globalDiagonal,embedMatrix_apply _ (balancedJoin_injective k),codeTuple_fixed]
  simp only [(codeTuple_injective k).eq_iff,eq_comm]

/-- The literal coordinate-column matrix C_k from the paper. -/
def codeColumns (k : ℕ) : Matrix (State (blockWidth k) (2*k)) (CodeBits k) ℚ :=
  coordinateColumns (rawCode k)

/-- Multiplying by coordinate columns selects the corresponding actual entries. -/
theorem coordinateColumns_compress {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (e : α → ι) (M : Matrix ι ι ℚ) :
    (coordinateColumns e).transpose * M * coordinateColumns e = M.submatrix e e := by
  ext a b
  simp [Matrix.mul_apply,Matrix.transpose_apply,coordinateColumns]

/-- First identity of Lemma5.3 for the actual global projection and actual raw code states. -/
theorem codeColumns_projection (k : ℕ) :
    (codeColumns k).transpose * globalProjection k * codeColumns k = 1 := by
  rw [codeColumns,coordinateColumns_compress]
  ext x y
  exact (globalProjection_rawCode k x y).trans (Matrix.one_apply ..).symm

end HiddenCircuits
