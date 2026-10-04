import HiddenCircuits.GraphReduction.UnitIntervalResidualRecognition

/-! A component's final remaining mask is exactly deletion of its emitted
labels. Residual-only recognition may reuse that actual mask directly. -/
namespace HiddenCircuits.GraphReduction.UnitIntervalComponentResidual
open UnitIntervalBitMasks
variable {n : ℕ}

lemma mask_ext (a b : List Bool) (ha : a.length=n) (hb : b.length=n)
    (h : active (n:=n) a = active b) : a=b := by
  apply List.ext_getElem
  · omega
  · intro i hi hj
    let v : Fin n := ⟨i,by omega⟩
    have he : UnitIntervalBitMasks.read a v = UnitIntervalBitMasks.read b v := by
      apply Bool.eq_iff_iff.mpr
      have hh : v ∈ active a ↔ v ∈ active b := by rw [h]
      simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and] using hh
    simpa only [UnitIntervalBitMasks.read,v,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj,Option.getD_some] using he

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma run_remaining (alive : List Bool) (A : Finset (Fin n)) (fuel : ℕ) (s : UnitIntervalBitMasks.State n)
    (hr : s.remaining.length=n) (hi : active s.remaining = A \ s.order.toFinset) :
    (UnitIntervalBitMasks.run G alive fuel s).remaining.length=n ∧
      active (UnitIntervalBitMasks.run G alive fuel s).remaining =
        A \ (UnitIntervalBitMasks.run G alive fuel s).order.toFinset := by
  induction fuel generalizing s with
  | zero => exact ⟨hr,hi⟩
  | succ fuel ih =>
    simp only [UnitIntervalBitMasks.run]
    split
    · exact ⟨hr,hi⟩
    · rename_i y hy
      split
      · exact ⟨hr,hi⟩
      · apply ih
        · exact (set_length _ _ _).trans hr
        · rw [active_set_false _ hr,hi]
          ext v
          simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
            Finset.mem_erase,Finset.mem_sdiff,Finset.mem_union,Finset.mem_insert,Finset.notMem_empty,or_false]
          tauto

/-- This equality covers the actual Boolean lists, not only their active sets. -/
theorem component_remaining_eq (alive : List Bool) (ha : alive.length=n) (root : Fin n) :
    (UnitIntervalBitRecognition.componentState G alive root).remaining =
      UnitIntervalBitRecognition.eraseList alive (UnitIntervalBitRecognition.component G alive root) := by
  have hi : active (set alive root false) = active (n:=n) alive \ ([root] : List (Fin n)).toFinset := by
    rw [active_set_false _ ha]
    ext v
    simp [and_comm]
  have hh := run_remaining G alive (active alive) n
    (⟨[root],ofFinset {root},set alive root false⟩ : UnitIntervalBitMasks.State n)
    ((set_length _ _ _).trans ha) hi
  change (UnitIntervalBitRecognition.componentState G alive root).remaining.length=n ∧
    active (UnitIntervalBitRecognition.componentState G alive root).remaining =
      active alive \ (UnitIntervalBitRecognition.component G alive root).toFinset at hh
  apply mask_ext _ _ hh.1 ((UnitIntervalBitRecognition.eraseList_length _ _).trans ha)
  rw [hh.2,UnitIntervalBitRecognition.active_eraseList _ ha]

/-- The machine can retain a candidate's actual remaining mask after the checker passes. -/
def step (alive : List Bool) : List Bool :=
  match UnitIntervalBitRecognition.goodRoot G alive with
  | none => alive
  | some root => (UnitIntervalBitRecognition.componentState G alive root).remaining

lemma step_eq (alive : List Bool) (ha : alive.length=n) :
    step G alive = UnitIntervalResidualRecognition.step G alive := by
  unfold step UnitIntervalResidualRecognition.step
  cases he : UnitIntervalBitRecognition.goodRoot G alive with
  | none => rfl
  | some root => exact component_remaining_eq G alive ha root
lemma step_length (alive : List Bool) (ha : alive.length=n) : (step G alive).length=n := by
  rw [step_eq G alive ha]
  unfold UnitIntervalResidualRecognition.step
  split
  · exact ha
  · exact (UnitIntervalBitRecognition.eraseList_length _ _).trans ha

def run : ℕ → List Bool → List Bool
  | 0,alive => alive
  | fuel+1,alive => run fuel (step G alive)

lemma run_eq (fuel : ℕ) (alive : List Bool) (ha : alive.length=n) :
    run G fuel alive = UnitIntervalResidualRecognition.run G fuel alive := by
  induction fuel generalizing alive with
  | zero => rfl
  | succ fuel ih =>
    rw [run,ih _ (step_length G alive ha),step_eq G alive ha]
    rfl

/-- Acceptance of the actual residual-mask iteration is exactly the semantic
real unit-interval class, without accumulating a global order. -/
theorem accepts_iff :
    UnitIntervalBitMasks.count (n:=n) (run G n (List.replicate n true)) = 0 ↔
      RealUnitInterval.UnitIntervalGraph G := by
  rw [run_eq G n _ (by simp)]
  exact UnitIntervalResidualRecognition.accepts_iff G

end HiddenCircuits.GraphReduction.UnitIntervalComponentResidual
