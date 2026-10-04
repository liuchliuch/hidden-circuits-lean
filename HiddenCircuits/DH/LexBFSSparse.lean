import HiddenCircuits.DH.LexBFSSemantics
import Mathlib.Data.List.Sort

/-! List-level correctness of sparse, interleaved neighbor moves.
The pointer engine implements the erase/append transitions in constant time; no complexity
claim is attached to the extensional list operations used in this specification. -/
namespace HiddenCircuits.DH.LexBFSSparse
open LexBFSModel

/-- One old cell's sparse update, ignoring row vertices absent from this cell. -/
def moveRow {V : Type*} [DecidableEq V] : List V → List V → List V → List V × List V
  | [],residual,companion => (residual,companion)
  | v::row,residual,companion =>
      if v ∈ residual then moveRow row (residual.erase v) (companion++[v])
      else moveRow row residual companion

/-- The loop processes only actual listed neighbors. Its prefix invariant is exact:
residual removes the processed row, and companion appends the processed row's intersection. -/
theorem moveRow_spec {V : Type*} [DecidableEq V] (row cell companion : List V)
    (hr : row.Nodup) (hc : cell.Nodup) :
    moveRow row cell companion =
      (cell.filter (fun v => decide (v ∉ row)),companion++row.filter (fun v => decide (v ∈ cell))) := by
  induction row generalizing cell companion with
  | nil => simp [moveRow]
  | cons v row ih =>
    obtain ⟨hvn,hr⟩ := List.nodup_cons.mp hr
    by_cases hv : v ∈ cell
    · rw [moveRow,if_pos hv,ih (cell.erase v) (companion++[v]) hr (hc.erase v)]
      have hselect : row.filter (fun u => decide (u ∈ cell.erase v)) =
          row.filter (fun u => decide (u ∈ cell)) := by
        apply List.filter_congr
        intro u hu
        have huv : u≠v := fun he => hvn (he ▸ hu)
        simp [hc.mem_erase_iff,huv]
      have hres : (cell.erase v).filter (fun u => decide (u ∉ row)) =
          cell.filter (fun u => decide (u ∉ v::row)) := by
        rw [hc.erase_eq_filter,List.filter_filter]
        apply List.filter_congr
        intro u hu
        simp only [List.mem_cons,not_or]
        by_cases huv : u=v <;> by_cases hur : u∈row <;> simp [huv,hur]
      rw [hselect,hres]
      simp [hv,List.append_assoc]
    · rw [moveRow,if_neg hv,ih cell companion hr hc]
      have hres : cell.filter (fun u => decide (u ∉ row)) =
          cell.filter (fun u => decide (u ∉ v::row)) := by
        apply List.filter_congr
        intro u hu
        have huv : u≠v := fun he => hv (he ▸ hu)
        simp [huv]
      rw [hres]
      simp [hv]

/-- Any prefix can be processed and then resumed; other old cells' moves do not alter this state. -/
lemma moveRow_append {V : Type*} [DecidableEq V] (left right cell companion : List V) :
    moveRow (left++right) cell companion =
      moveRow right (moveRow left cell companion).1 (moveRow left cell companion).2 := by
  induction left generalizing cell companion with
  | nil => rfl
  | cons v left ih =>
    simp only [List.cons_append,moveRow]
    split <;> exact ih _ _

/-- Increasing row order and increasing cell order induce the same intersection order. -/
lemma intersection_order {V : Type*} [LinearOrder V] (row cell : List V)
    (hr : row.Pairwise (· < ·)) (hc : cell.Pairwise (· < ·)) :
    row.filter (fun v => decide (v ∈ cell)) = cell.filter (fun v => decide (v ∈ row)) := by
  apply (hr.filter _).eq_of_mem_iff (hc.filter _)
  intro v
  simp [and_comm]

/-- An old cell's interleaved sparse moves are exactly stable partition refinement. -/
theorem moveRow_refine {V : Type*} [LinearOrder V] (first : Bool) (row cell : List V)
    (hr : row.Pairwise (· < ·)) (hc : cell.Pairwise (· < ·)) :
    let q := moveRow row cell []
    (if first then nonemptyCell q.2 ++ nonemptyCell q.1 else
      nonemptyCell q.1 ++ nonemptyCell q.2) =
      splitCell first (fun v => decide (v ∈ row)) cell := by
  rw [moveRow_spec row cell [] hr.nodup hc.nodup]
  simp only [List.nil_append,intersection_order row cell hr hc]
  cases first <;> simp [splitCell]

/-- Whole-partition consequence, independent of how updates to different old cells interleave. -/
theorem sparse_partition_refine {V : Type*} [LinearOrder V] (first : Bool)
    (row : List V) (p : Partition V) (hr : row.Pairwise (· < ·))
    (hp : ∀ cell ∈ p, cell.Pairwise (· < ·)) :
    p.flatMap (fun cell => let q := moveRow row cell []
      if first then nonemptyCell q.2 ++ nonemptyCell q.1 else
        nonemptyCell q.1 ++ nonemptyCell q.2) =
      refine first (fun v => decide (v ∈ row)) p := by
  unfold refine
  induction p with
  | nil => rfl
  | cons cell p ih =>
    simp only [List.flatMap_cons]
    rw [moveRow_refine first row cell hr (hp cell List.mem_cons_self)]
    rw [ih (fun c hc => hp c (List.mem_cons_of_mem _ hc))]

end HiddenCircuits.DH.LexBFSSparse
