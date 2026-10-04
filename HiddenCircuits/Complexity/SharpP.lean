import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Machine-grounded counting complexity

The verifier in `SharpP` is an actual finite-stack Turing machine from mathlib,
with its step-count bounded by a natural-coefficient polynomial. Neither a
counting problem nor a hardness assertion occurs in this definition.

The binary certificate length is fixed by the input length. Padding is therefore
canonical: this definition counts every certificate exactly once.
-/
namespace HiddenCircuits.Complexity

abbrev BitString := List Bool

/-- Self-delimiting binary pairing. Every bit of the first component is preceded
by `true`; the single `false` delimiter introduces the second component. -/
def pairBits : BitString → BitString → BitString
  | [], y => false :: y
  | b :: x, y => true :: b :: pairBits x y

def unpairBits : BitString → Option (BitString × BitString)
  | false :: y => some ([], y)
  | true :: b :: z => (unpairBits z).map (fun xy => (b :: xy.1, xy.2))
  | _ => none

@[simp] theorem unpair_pairBits (x y : BitString) :
    unpairBits (pairBits x y) = some (x,y) := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairBits, unpairBits, ih]

@[simp] theorem pairBits_length (x y : BitString) :
    (pairBits x y).length = 2 * x.length + y.length + 1 := by
  induction x with
  | nil => simp [pairBits]
  | cons b x ih => simp [pairBits, ih]; omega

theorem pairBits_injective : Function.Injective (fun xy : BitString × BitString =>
    pairBits xy.1 xy.2) := by
  intro x y h
  have := congrArg unpairBits h
  simpa using this

/-- The ordinary binary encoding of a pair, with an explicit inverse. -/
def pairEncoding : Computability.FinEncoding (BitString × BitString) where
  Γ := Bool
  ΓFin := inferInstance
  encode xy := pairBits xy.1 xy.2
  decode := unpairBits
  decode_encode xy := unpair_pairBits xy.1 xy.2

/-- Genuine polynomial-time binary computation, using mathlib's finite TM2
machine and its operational `EvalsToInTime` semantics. -/
def PolyTime (f : BitString → BitString) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime id id f)

/-- A polynomial-time Boolean verifier on one binary string. -/
def PolyVerifier (v : BitString → Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

/-- Number of accepted length-`m` certificates; these are actual bit strings,
with no quotient by computations and no multiplicity from padding. -/
noncomputable def certificateCount (v : BitString → Bool) (x : BitString) (m : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin m → Bool // v (pairBits x (List.ofFn w)) = true}

/-- The standard polynomially balanced verifier definition of #P, with an actual
polynomial-time finite Turing machine rather than an assumed complexity flag. -/
def SharpP (f : BitString → ℕ) : Prop :=
  ∃ (p : Polynomial ℕ) (v : BitString → Bool), PolyVerifier v ∧
    ∀ x, f x = certificateCount v x (p.eval x.length)

theorem certificateCount_le (v : BitString → Bool) (x : BitString) (m : ℕ) :
    certificateCount v x m ≤ 2 ^ m := by
  classical
  unfold certificateCount
  calc
    Fintype.card {w : Fin m → Bool // v (pairBits x (List.ofFn w)) = true}
        ≤ Fintype.card (Fin m → Bool) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = 2 ^ m := by simp

/-- Every #P value has polynomially many binary digits. This is derived from
certificate counting, independently of any target problem. -/
theorem SharpP.value_bound {f : BitString → ℕ} (hf : SharpP f) :
    ∃ p : Polynomial ℕ, ∀ x, f x ≤ 2 ^ p.eval x.length := by
  obtain ⟨p,v,_,hv⟩ := hf
  exact ⟨p, fun x => (hv x).trans_le (certificateCount_le v x _)⟩

/-- The full verifier input has a proved polynomial size when certificates do. -/
theorem verifier_input_length (p : Polynomial ℕ) (x : BitString)
    (w : Fin (p.eval x.length) → Bool) :
    (pairBits x (List.ofFn w)).length = 2 * x.length + p.eval x.length + 1 := by
  simp

theorem encodePosNum_length (n : PosNum) :
    (Computability.encodePosNum n).length = n.natSize := by
  induction n <;> simp [Computability.encodePosNum, PosNum.natSize, *]

theorem encodeNum_length (n : Num) :
    (Computability.encodeNum n).length = n.natSize := by
  cases n <;> simp [Computability.encodeNum, Num.natSize, encodePosNum_length]

/-- Actual binary natural-number output length agrees with `Nat.size`. -/
theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  unfold Computability.encodeNat
  rw [encodeNum_length, Num.natSize_to_nat]
  simp

theorem SharpP.binary_output_bound {f : BitString → ℕ} (hf : SharpP f) :
    ∃ p : Polynomial ℕ, ∀ x, (Computability.encodeNat (f x)).length ≤ p.eval x.length := by
  obtain ⟨p,hp⟩ := hf.value_bound
  refine ⟨p+1, fun x => ?_⟩
  rw [encodeNat_length]
  have h := Nat.size_le_size (hp x)
  rw [Nat.size_pow] at h
  simpa using h

end HiddenCircuits.Complexity
