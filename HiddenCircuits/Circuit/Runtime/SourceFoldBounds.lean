import HiddenCircuits.Circuit.Runtime.FramedFor
import HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator

/-! Literal unary iteration agrees with list folds, including
rows whose bodies consume an entire concrete list of rational items. -/
namespace HiddenCircuits.Circuit.Runtime.SourceFold
open HiddenCircuits.Complexity BinaryArithmetic HiddenCircuits.DH.Runtime

def stepAt {α D : Type*} (xs : List α) (default : α) (step : D→α→D) (i : ℕ) (a : D) : D := step a (xs[i]?.getD default)
lemma iterate_take {α D : Type*} (xs : List α) (default : α) (step : D→α→D) (i m : ℕ) (a : D) (h : i+m≤xs.length) :
    UnaryFor.iterate (stepAt xs default step) i m a=((xs.drop i).take m).foldl step a := by
  induction m generalizing i a with
  | zero => simp [UnaryFor.iterate]
  | succ m ih =>
    have hi : i<xs.length := by omega
    rw [UnaryFor.iterate,ih (i+1) _ (by omega),List.drop_eq_getElem_cons hi,List.take_succ_cons,List.foldl_cons]
    simp only [stepAt,List.getElem?_eq_getElem hi,Option.getD_some]
lemma iterate_all {α D : Type*} (xs : List α) (default : α) (step : D→α→D) (a : D) :
    UnaryFor.iterate (stepAt xs default step) 0 xs.length a=xs.foldl step a := by
  simpa using iterate_take xs default step 0 xs.length a (by omega)
lemma iterate_rows (xs : List (List RationalAccumulator.Ratio)) (a : RationalAccumulator.Ratio) :
    UnaryFor.iterate (stepAt xs [] RationalAccumulator.run) 0 xs.length a=RationalAccumulator.run a xs.flatten := by
  rw [iterate_all,RationalAccumulator.foldl_run_flatten]
lemma remaining_rows {C : ℕ} {a : RationalAccumulator.Ratio} {xs : List (List RationalAccumulator.Ratio)}
    {tail : List RationalAccumulator.Ratio} {i : ℕ} (hi : i<xs.length)
    (h : RationalAccumulator.BitBound C a ((xs.drop i).flatten++tail)) :
    RationalAccumulator.BitBound C a (xs[i]++((xs.drop (i+1)).flatten++tail)) := by
  rwa [List.drop_eq_getElem_cons hi,List.flatten_cons,List.append_assoc] at h
end HiddenCircuits.Circuit.Runtime.SourceFold
