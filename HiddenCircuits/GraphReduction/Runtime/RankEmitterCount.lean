import HiddenCircuits.GraphReduction.Runtime.RankEmitterEncoding
import HiddenCircuits.GraphReduction.PermutationRankCompression

/-! Each actual unary row count is the number of preceding endpoints. -/
namespace HiddenCircuits.GraphReduction.Runtime.RankEmitter
open Complexity
open scoped BigOperators

lemma rowCount_sum (edge : ℕ→ℕ→Bool) (i j m : ℕ) :
    rowCount edge i j m=((List.range' j m).map (fun r => if edge i r then 1 else 0)).sum := by
  induction m generalizing j with
  | zero => simp [rowCount]
  | succ m ih => simp [rowCount,List.range'_succ,ih]
lemma rowCount_endpoint {n : ℕ} (edge : ℕ→ℕ→Bool) (f : Fin n→ℕ) (i : Fin n)
    (he : ∀j:Fin n,edge i.val j.val=decide (f j<f i)) :
    rowCount edge i.val 0 n=endpointCount f (f i) := by
  rw [rowCount_sum,←List.range_eq_range',←List.map_coe_finRange_eq_range (n:=n)]
  simp only [List.map_map,Function.comp_def]
  rw [←Fin.sum_univ_def]
  unfold endpointCount
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j]
  simp

theorem bits_eq_endpointCount (n : ℕ) (edge : ℕ→ℕ→Bool) (f : Fin n→ℕ)
    (he : ∀i j:Fin n,edge i.val j.val=decide (f j<f i)) :
    bits n edge=encodeBitList (List.ofFn (fun i => List.replicate (endpointCount f (f i)) true)) := by
  unfold bits words
  rw [←List.map_coe_finRange_eq_range (n:=n)]
  simp only [List.map_map,Function.comp_def,List.ofFn_eq_map]
  apply congrArg encodeBitList
  apply List.map_congr_left
  intro i hi
  rw [rowCount_endpoint edge f i (he i)]
end HiddenCircuits.GraphReduction.Runtime.RankEmitter
