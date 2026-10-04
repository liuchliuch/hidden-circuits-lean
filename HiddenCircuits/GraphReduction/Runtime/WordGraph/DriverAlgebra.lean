import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryAlgebra
import HiddenCircuits.Complexity.BinaryArithmetic.RatioIteration

/-! Fresh reconstruction: actual graph-count ratio rows and exact indexed fold correspondence. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverAlgebra
open Complexity BinaryArithmetic DH.Runtime.UnaryFor

noncomputable def row (w : WordInstance) (t : Fin (Recovery.degree w+1)) : List (ℤ×ℤ) :=
  (List.finRange (Recovery.innerDegree w t+1)).map (fun s => Recovery.ratio w ⟨t,s⟩ (perfectMatchingCount (Recovery.query w ⟨t,s⟩).2.graph))
noncomputable def rows (w : WordInstance) : List (List (ℤ×ℤ)) :=
  (List.finRange (Recovery.degree w+1)).map (row w)


@[simp] lemma row_length (w : WordInstance) (t : Fin (Recovery.degree w+1)) :
    (row w t).length=Recovery.innerDegree w t+1 := by simp [row]
@[simp] lemma rows_length (w : WordInstance) :
    (rows w).length=Recovery.degree w+1 := by simp [rows]
lemma flatten_rows (w : WordInstance) : (rows w).flatten=Recovery.terms w := by
  simp only [rows,Recovery.terms,Recovery.indices,List.sigma,List.map_flatMap,List.map_map,Function.comp_def]
  rfl
lemma row_get (w : WordInstance) (t : Fin (Recovery.degree w+1))
    (s : ℕ) (hs : s<Recovery.innerDegree w t+1) :
    (row w t)[s]?.getD (0,1)=Recovery.ratio w ⟨t,⟨s,hs⟩⟩ (perfectMatchingCount (Recovery.query w ⟨t,⟨s,hs⟩⟩).2.graph) := by
  have hlen : s<(List.finRange (Recovery.innerDegree w t+1)).length := by simpa using hs
  have he : (List.finRange (Recovery.innerDegree w t+1))[s]=⟨s,hs⟩ := List.getElem_finRange hlen
  simp only [row,List.getElem?_map,List.getElem?_eq_getElem hlen,Option.map_some,Option.getD_some,he]
lemma rows_get (w : WordInstance) (t : ℕ) (ht : t<Recovery.degree w+1) :
    (rows w)[t]?.getD []=row w ⟨t,ht⟩ := by simp [rows,List.getElem?_eq_getElem,ht]
lemma inner_iterate (w : WordInstance) (t : Fin (Recovery.degree w+1)) (a : ℤ×ℤ) :
    iterate (fun s a => RationalAccumulator.step a ((row w t)[s]?.getD (0,1))) 0 (Recovery.innerDegree w t+1) a=
      RationalAccumulator.run a (row w t) := by
  simpa only [row_length] using DriverAlgebra.iterate_lookup RationalAccumulator.step (row w t) (0,1) a
lemma outer_iterate (w : WordInstance) (a : ℤ×ℤ) :
    iterate (fun t a => RationalAccumulator.run a ((rows w)[t]?.getD [])) 0 (Recovery.degree w+1) a=
      RationalAccumulator.run a (Recovery.terms w) := by
  have h := DriverAlgebra.iterate_lookup RationalAccumulator.run (rows w) [] a
  rw [RationalAccumulator.foldl_run_flatten,flatten_rows,rows_length] at h
  exact h
end HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverAlgebra
