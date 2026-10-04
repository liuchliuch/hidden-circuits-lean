import HiddenCircuits.Circuit.SpectralIntegerWeights
import HiddenCircuits.Complexity.BinaryArithmetic.Parity
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsLoop

/-! Exact triangular target values at0 and−1, in the spectral node order. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTargets
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic

def base (mode : Bool) : ℤ := if mode then -1 else 0
def row (mode : Bool) : ℕ → List ℤ
  | 0 => []
  | n+1 => (base mode)^n::row mode n
def triangle (mode : Bool) : ℕ → List ℤ
  | 0 => []
  | n+1 => row mode (n+1)++triangle mode n

@[simp] theorem row_length (mode : Bool) (n : ℕ) : (row mode n).length=n := by
  induction n <;> simp_all [row]

theorem row_eq_range (mode : Bool) (n : ℕ) : row mode n=(List.range n).map (fun j => (base mode)^(n-1-j)) := by
  induction n with
  | zero => simp [row]
  | succ n ih =>
    rw [row,ih,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.add_sub_cancel,Nat.sub_zero]
    congr 1
    apply List.map_congr_left
    intro j hj
    have he : n-1-j=n-(j+1) := by omega
    simp only [Function.comp_apply,he]

theorem triangle_eq_range (mode : Bool) (n : ℕ) :
    triangle mode n=(List.range n).flatMap (fun a => row mode (n-a)) := by
  induction n with
  | zero => simp [triangle]
  | succ n ih =>
    rw [triangle,ih,List.range_succ_eq_map]
    simp only [List.flatMap_cons,List.flatMap_map,Function.comp_apply,Nat.sub_zero,Nat.succ_eq_add_one,Nat.add_sub_add_right]

theorem triangle_length_le (mode : Bool) (n : ℕ) : (triangle mode n).length≤n*n := by
  induction n with
  | zero => simp [triangle]
  | succ n ih => simp only [triangle,List.length_append,row_length];nlinarith

def weights (g : ℕ) (mode : Bool) : List ℤ :=
  (spectralIndices g).map (fun i => (base mode)^(g-i.1.val-i.2.val))

theorem triangle_weights (g : ℕ) (mode : Bool) : triangle mode (g+1)=weights g mode := by
  rw [triangle_eq_range]
  simp only [weights,spectralIndices,List.sigma,List.map_flatMap,List.map_map]
  rw [←List.map_coe_finRange_eq_range (n:=g+1),List.flatMap_map]
  apply List.flatMap_congr
  intro a ha
  rw [row_eq_range]
  have he : g+1-a.val=g-a.val+1 := by have := a.isLt;omega
  rw [he,←List.map_coe_finRange_eq_range (n:=g-a.val+1),List.map_map]
  apply List.map_congr_left
  intro b hb
  simp [Function.comp_apply]

theorem target_signed_length (mode : Bool) (n : ℕ) : (signedBits ((base mode)^n)).length≤2 := by
  cases mode with
  | false =>
    cases n with
    | zero => decide +kernel
    | succ n =>
      rw [show (base false)^(n+1)=(0:ℤ) by simp [base]]
      decide +kernel
  | true =>
    change (signedBits ((-1:ℤ)^n)).length≤2
    rw [←signedNat_parity]
    cases parityBit n <;> decide +kernel

theorem weight_stream_length (g : ℕ) (mode : Bool) :
    (encodeBitList ((weights g mode).map signedBits)).length≤6*(g+1)^2 := by
  have h := encodedWords_length_le ((weights g mode).map signedBits) 2 (by
    intro w hw;obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
    exact target_signed_length mode _)
  have hl := triangle_length_le mode (g+1)
  rw [triangle_weights] at hl
  simp only [List.length_map] at h
  nlinarith
end HiddenCircuits.Circuit.Runtime.SpectralTargets
