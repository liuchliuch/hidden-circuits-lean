import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrellaInner
import HiddenCircuits.GraphReduction.UnitIntervalUmbrellaScan

/-! Correctness of the physically traversed tail checker, including its use on
the reversed label array emitted by the component scanner. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
open Complexity DH.Runtime.PairCheck

lemma inner_eq {n : ℕ} (G : MatrixData n) (u v : Fin n) (ls : List (Fin n)) :
    inner G u v ls = UnitIntervalUmbrellaScan.inner G.edge u v ls := rfl
lemma middle_eq {n : ℕ} (G : MatrixData n) (u : Fin n) (ls : List (Fin n)) :
    middle G u ls = UnitIntervalUmbrellaScan.middle G.edge u ls := by
  induction ls with
  | nil => rfl
  | cons v vs ih => simp only [middle,UnitIntervalUmbrellaScan.middle,inner_eq,ih]
lemma check_eq {n : ℕ} (G : MatrixData n) (ls : List (Fin n)) :
    check G ls = UnitIntervalUmbrellaScan.umbrella G.edge ls := by
  induction ls with
  | nil => rfl
  | cons u us ih => simp only [check,UnitIntervalUmbrellaScan.umbrella,middle_eq,ih]

/-- The exact finite Boolean checker agrees with the proved umbrella-order predicate. -/
theorem check_ofGraph_iff {n : ℕ} (G : MatrixGraph n) (ls : List (Fin n)) :
    check (MatrixData.ofGraph G) ls = true ↔ UnitIntervalOrder.ListUmbrella G.graph ls := by
  rw [check_eq]
  change UnitIntervalUmbrellaScan.umbrella G.edge ls = true ↔ _
  have he : (fun u v => decide (G.graph.Adj u v)) = G.edge := by
    funext u v
    change decide (G.edge u v = true) = G.edge u v
    simp
  have h := UnitIntervalUmbrellaScan.umbrella_correct G.graph ls
  rw [he] at h
  exact h

/-- No array reversal or extra ordering certificate is needed at runtime. -/
theorem check_reverse_ofGraph_iff {n : ℕ} (G : MatrixGraph n) (ls : List (Fin n)) :
    check (MatrixData.ofGraph G) ls.reverse = true ↔ UnitIntervalOrder.ListUmbrella G.graph ls := by
  rw [check_ofGraph_iff,UnitIntervalUmbrellaScan.listUmbrella_reverse_iff]

theorem check_reverse_ofGraph {n : ℕ} (G : MatrixGraph n) (ls : List (Fin n)) :
    check (MatrixData.ofGraph G) ls.reverse = check (MatrixData.ofGraph G) ls := by
  apply Bool.eq_iff_iff.mpr
  rw [check_reverse_ofGraph_iff,check_ofGraph_iff]

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
