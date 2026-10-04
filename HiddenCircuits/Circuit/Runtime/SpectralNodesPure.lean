import HiddenCircuits.Circuit.SpectralIntegerWeights
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! Ordered triangular node streams, independently of their finite bit program. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralNodes
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic

def row (x : ℤ) : ℕ → List ℤ
  | 0 => []
  | n+1 => x :: row (x*9) n

def triangle (x : ℤ) : ℕ → List ℤ
  | 0 => []
  | n+1 => row x (n+1) ++ triangle (x*4) n

@[simp] theorem row_length (x : ℤ) (n : ℕ) : (row x n).length=n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [row,ih]

theorem row_eq_range (x : ℤ) (n : ℕ) : row x n=(List.range n).map (fun b => x*9^b) := by
  induction n generalizing x with
  | zero => simp [row]
  | succ n ih =>
    rw [row,ih,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map, pow_zero,mul_one]
    congr 1
    apply List.map_congr_left
    intro b hb
    simp only [Function.comp_apply,pow_succ]
    ring

theorem triangle_length_le (x : ℤ) (n : ℕ) : (triangle x n).length≤n*n := by
  induction n generalizing x with
  | zero => simp [triangle]
  | succ n ih =>
    simp only [triangle,List.length_append,row_length]
    have h := ih (x*4)
    nlinarith

theorem triangle_eq_range (x : ℤ) (n : ℕ) :
    triangle x n=(List.range n).flatMap (fun a => row (x*4^a) (n-a)) := by
  induction n generalizing x with
  | zero => simp [triangle]
  | succ n ih =>
    rw [triangle,ih,List.range_succ_eq_map]
    simp only [List.flatMap_cons,List.flatMap_map,Function.comp_apply,pow_zero,mul_one,Nat.sub_zero]
    congr 1
    apply List.flatMap_congr
    intro a ha
    simp only [Nat.succ_eq_add_one,Nat.add_sub_add_right,pow_succ]
    congr 1
    ring

theorem triangle_spectral (g : ℕ) :
    triangle 1 (g+1)=(spectralIndices g).map spectralIntegerNode := by
  rw [triangle_eq_range]
  simp only [spectralIndices,List.sigma,List.map_flatMap,List.map_map]
  rw [←List.map_coe_finRange_eq_range (n:=g+1),List.flatMap_map]
  apply List.flatMap_congr
  intro a ha
  rw [row_eq_range]
  have he : g+1-a.val=g-a.val+1 := by have := a.isLt;omega
  rw [he,←List.map_coe_finRange_eq_range (n:=g-a.val+1),List.map_map]
  apply List.map_congr_left
  intro b hb
  simp [Function.comp_apply,spectralIntegerNode,spectralNode]

end HiddenCircuits.Circuit.Runtime.SpectralNodes
