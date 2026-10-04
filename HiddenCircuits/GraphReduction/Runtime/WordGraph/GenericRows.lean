import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverAlgebra

/-! Pure row lists for instantiating the same concrete loop with another target cell. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericDriver
open Complexity BinaryArithmetic DH.Runtime.UnaryFor

def row (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) (t : Fin (Recovery.degree w+1)) : List (ℤ×ℤ) :=
  (List.finRange (Recovery.innerDegree w t+1)).map (fun s => term ⟨t,s⟩)
def rows (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) : List (List (ℤ×ℤ)) :=
  (List.finRange (Recovery.degree w+1)).map (row w term)
def terms (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) : List (ℤ×ℤ) := (Recovery.indices w).map term

@[simp] lemma row_length (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) (t : Fin (Recovery.degree w+1)) :
    (row w term t).length=Recovery.innerDegree w t+1 := by simp [row]
@[simp] lemma rows_length (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) :
    (rows w term).length=Recovery.degree w+1 := by simp [rows]
lemma flatten_rows (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) : (rows w term).flatten=terms w term := by
  simp only [rows,terms,Recovery.indices,List.sigma,List.map_flatMap,List.map_map,Function.comp_def]
  rfl
lemma row_get (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) (t : Fin (Recovery.degree w+1))
    (s : ℕ) (hs : s<Recovery.innerDegree w t+1) :
    (row w term t)[s]?.getD (0,1)=term ⟨t,⟨s,hs⟩⟩ := by
  have hlen : s<(List.finRange (Recovery.innerDegree w t+1)).length := by simpa using hs
  have he : (List.finRange (Recovery.innerDegree w t+1))[s]=⟨s,hs⟩ := List.getElem_finRange hlen
  simp only [row,List.getElem?_map,List.getElem?_eq_getElem hlen,Option.map_some,Option.getD_some,he]
lemma rows_get (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) (t : ℕ) (ht : t<Recovery.degree w+1) :
    (rows w term)[t]?.getD []=row w term ⟨t,ht⟩ := by simp [rows,List.getElem?_eq_getElem,ht]
lemma inner_iterate (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) (t : Fin (Recovery.degree w+1)) (a : ℤ×ℤ) :
    iterate (fun s a => RationalAccumulator.step a ((row w term t)[s]?.getD (0,1))) 0 (Recovery.innerDegree w t+1) a=
      RationalAccumulator.run a (row w term t) := by
  simpa only [row_length] using DriverAlgebra.iterate_lookup RationalAccumulator.step (row w term t) (0,1) a
lemma outer_iterate (w : WordInstance) (term : Recovery.Index w → ℤ×ℤ) (a : ℤ×ℤ) :
    iterate (fun t a => RationalAccumulator.run a ((rows w term)[t]?.getD [])) 0 (Recovery.degree w+1) a=
      RationalAccumulator.run a (terms w term) := by
  have h := DriverAlgebra.iterate_lookup RationalAccumulator.run (rows w term) [] a
  rw [RationalAccumulator.foldl_run_flatten,flatten_rows,rows_length] at h
  exact h
end HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericDriver
