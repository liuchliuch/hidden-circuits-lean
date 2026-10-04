import HiddenCircuits.GraphReduction.UnitIntervalRecovery
import HiddenCircuits.GraphReduction.UnitIntervalIntegerGraph
import HiddenCircuits.GraphReduction.CliqueProbeDecidable

/-! Completed mathematical Section10 query construction and PairEval recovery. -/
namespace HiddenCircuits.GraphReduction

/-- Every actual even-sized oracle query has a literal unit-length interval representation,
polynomially many vertices and explicitly bounded integer endpoints before rescaling. -/
theorem unitIntervalPairQuery_valid {p : ℕ} (w : List (CutPair p)) (hw : w≠[])
    (S T : State (2*p) p) (t : Fin (2*p*w.length+1)) :
    Nonempty {D : UnitInterval.Representation (unitIntervalQueryGraph (fun r => w.get r) S T (2*t.val)) //
      D.length=1} ∧
    Fintype.card (UnitOriginalVertex p w.length S T ⊕ (Fin (w.length+1) × Fin (2*t.val)))≤
      4*p*w.length*(w.length+2) ∧
    ∀ v : UnitOriginalVertex p w.length S T ⊕ (Fin (w.length+1) × Fin (2*t.val)),
      0≤unitQueryLeftInteger w v ∧
        unitQueryLeftInteger w v+UnitInterval.commonLength (2*p) w.length≤4000*(p+1)*(w.length+1)^2 :=
  ⟨⟨⟨unitIntervalQueryUnitRepresentation w S T (2*t.val),rfl⟩⟩,
    unitIntervalProbe_query_size (List.length_pos_iff.mpr hw) S T t,
    unitQuery_endpoint_bounds w S T (2*t.val)⟩

end HiddenCircuits.GraphReduction
