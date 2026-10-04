import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualArray
import HiddenCircuits.GraphReduction.MonotoneEndpointEncoding

/-! Exact canonical-byte identities for ordered row-zero/column-j deletion. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
open Complexity GraphReduction SamplerRuntime.EndpointFiber

lemma rows_eq_natWords {n : ℕ} (f : Fin n → ℕ) :
    MonotoneEndpointEncoding.rows f=natWords (List.ofFn f) := by
  simp [MonotoneEndpointEncoding.rows,natWords,List.map_ofFn,Function.comp_def,unary]
lemma rows_succ {n : ℕ} (f : Fin (n+1) → ℕ) :
    MonotoneEndpointEncoding.rows f=unary (f 0)::natWords (List.ofFn (fun i : Fin n => f i.succ)) := by
  rw [rows_eq_natWords,List.ofFn_succ]
  rfl
lemma residual_rows_lo {n : ℕ} (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) :
    MonotoneEndpointEncoding.rows (deleteFirst E j).lo=
      natWords ((List.ofFn (fun i : Fin n => E.lo i.succ)).map (dropBoundary j.val)) := by
  simp only [MonotoneEndpointEncoding.rows,natWords,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  rw [deleteFirst_lo]
lemma residual_rows_hi {n : ℕ} (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) :
    MonotoneEndpointEncoding.rows (deleteFirst E j).hi=
      natWords ((List.ofFn (fun i : Fin n => E.hi i.succ)).map (dropBoundary j.val)) := by
  simp only [MonotoneEndpointEncoding.rows,natWords,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  rw [deleteFirst_hi]

lemma endpoint_lo_bound {n : ℕ} (E : MonotoneEndpoints (n+1)) :
    ∀t∈List.ofFn (fun i : Fin n => E.lo i.succ),t ≤ n+1 := by
  intro t ht
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  exact (E.lo_le_hi i.succ).trans (E.hi_le i.succ)
lemma endpoint_hi_bound {n : ℕ} (E : MonotoneEndpoints (n+1)) :
    ∀t∈List.ofFn (fun i : Fin n => E.hi i.succ),t ≤ n+1 := by
  intro t ht
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  exact E.hi_le i.succ

lemma endpoint_array_length {n : ℕ} (E : MonotoneEndpoints n) :
    (encodeBitList (MonotoneEndpointEncoding.rows E.lo)).length ≤ 2*n*(n+1) ∧
      (encodeBitList (MonotoneEndpointEncoding.rows E.hi)).length ≤ 2*n*(n+1) := by
  constructor
  · rw [rows_eq_natWords]
    have h := natBits_length_bound (List.ofFn E.lo) n (by
      intro t ht;obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht;exact (E.lo_le_hi i).trans (E.hi_le i))
    simpa [natBits] using h
  · rw [rows_eq_natWords]
    have h := natBits_length_bound (List.ofFn E.hi) n (by
      intro t ht;obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht;exact E.hi_le i)
    simpa [natBits] using h
end HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
