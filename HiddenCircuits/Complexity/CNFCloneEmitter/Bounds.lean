import HiddenCircuits.Complexity.CNFCloneEmitter.CallbackCorrectness
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace HiddenCircuits.Complexity.CNFCloneEmitter
open Polynomial
variable {n m : ℕ}

lemma source_bounds (F : CNF n m) : n+m≤F.bits.length ∧ (Callback.payload F).length≤F.bits.length := by
  have h := CNFInput.encode_length_lower (⟨n,m,F⟩ : CNFInput)
  change 2*n+m+1≤F.bits.length at h
  constructor
  · omega
  · simp only [CNF.bits,pairBits_length,List.length_replicate,Callback.payload]
    omega

noncomputable def timeBound : Polynomial ℕ := 1000000*(X+1)^8

/-- A single explicit polynomial bounds dimension extraction, actual clone
adjacency callbacks, all row/column loops, output reversal and final cleanup.
Activities are unary inputs, so this bound also holds away from the recovery grid. -/
theorem cost_bound (F : CNF n m) (a b : ℕ) :
    let N := Callback.order (n:=n) (m:=m) a b
    30*F.bits.length+100*(n+m+a+b+1)^2+
      N*N*(Callback.time F a b+18)+41*N+(Callback.payload F).length+n+m+n*2*a+79 ≤
      timeBound.eval (F.bits.length+a+b) := by
  dsimp only
  let L := F.bits.length
  let S := L+a+b+1
  let N := Callback.order (n:=n) (m:=m) a b
  let P := (Callback.payload F).length
  have hsrc := source_bounds F
  have hnm : n+m≤L := hsrc.1
  have hP : P≤L := hsrc.2
  have hS : 0<S := by dsimp [S];omega
  have hLS : L≤S := by dsimp [S];omega
  have habS : a+b≤S := by dsimp [S];omega
  have hAS : n+m+a+b+1≤S := by dsimp [S];omega
  have hna := Nat.mul_le_mul_right a (show n≤L by omega)
  have hmb := Nat.mul_le_mul_right b (show m≤L by omega)
  have hprodLS := Nat.mul_le_mul hLS habS
  have hN : N≤2*S^2 := by dsimp [N,Callback.order];nlinarith
  have hcut : n*2*a≤N := by dsimp [N,Callback.order];omega
  have hNSq : N*N≤4*S^4 := calc
    N*N = N^2 := by ring
    _ ≤ (2*S^2)^2 := Nat.pow_le_pow_left hN 2
    _ = 4*S^4 := by ring
  have hB : P+n+m+N+a+b+1≤4*S^2 := by
    have hlin : P+n+m+a+b+1≤2*S := by dsimp [S];omega
    nlinarith
  have hT : Callback.time F a b≤160000*S^4 := calc
    Callback.time F a b = 10000*(P+n+m+N+a+b+1)^2 := rfl
    _ ≤ 10000*(4*S^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 2)
    _ = 160000*S^4 := by ring
  have hmatrix : N*N*(Callback.time F a b+18)≤640000*S^8+72*S^4 := calc
    _ ≤ (4*S^4)*(160000*S^4+18) := Nat.mul_le_mul hNSq (Nat.add_le_add_right hT 18)
    _ = _ := by ring
  have hA := Nat.pow_le_pow_left hAS 2
  have hlinear : 30*L+41*N+P+n+m+n*2*a+79≤184*S^2+32*S+79 := by
    have hPN : P+n+m≤2*L := by omega
    nlinarith
  have hS1 : S≤S^8 := by simpa using (Nat.pow_le_pow_right hS (show 1≤8 by decide))
  have hS2 : S^2≤S^8 := Nat.pow_le_pow_right hS (by decide)
  have hS4 : S^4≤S^8 := Nat.pow_le_pow_right hS (by decide)
  have hS0 : 1≤S^8 := by simpa using (Nat.pow_le_pow_right hS (show 0≤8 by decide))
  have hsmall : 30*L+41*N+P+n+m+n*2*a+79≤84*S^2+32*S+79 := by
    have hPN : P+n+m≤2*L := by omega
    nlinarith
  change 30*L+100*(n+m+a+b+1)^2+N*N*(Callback.time F a b+18)+41*N+P+n+m+n*2*a+79≤_
  simp only [timeBound,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤1000000*S^8
  omega

end HiddenCircuits.Complexity.CNFCloneEmitter
