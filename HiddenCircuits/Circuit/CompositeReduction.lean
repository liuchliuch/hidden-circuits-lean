import HiddenCircuits.Circuit.SourceCircuit
import HiddenCircuits.Circuit.SampleBounds

namespace HiddenCircuits.Circuit
open scoped BigOperators
noncomputable section

/-- The proved shared-parameter formula, containing only explicitly constructed WordEval instances. -/
def deltaWordFormula {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (x y : CodeBits n) : ℚ :=
  (geometricInterpolate (2*deltaOccurrences w)
    (fun u => closedScalar (w.map (DeltaGate.compileSample u.val)) *
      (compileWordInstance hn (w.map (DeltaGate.compileSample u.val)) x y).value)).eval 0

 theorem deltaWordFormula_correct {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (x y : CodeBits n) :
    deltaWordFormula hn w x y=deltaCircuitMatrix w x y := deltaCircuit_from_word_queries hn w x y

/-- The two-type spectral grid followed by shared conjugation, with no implicit oracle realization. -/
def constraintWordFormula {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (x y : CodeBits n) : ℚ :=
  ∑ r ∈ Finset.range (Fintype.card (SpectralIndex (forbidOccurrences w))),
    ∑ s ∈ Finset.range (Fintype.card (SpectralIndex (signOccurrences w))),
      targetCoefficient (forbidOccurrences w) 0 r * targetCoefficient (signOccurrences w) (-1) s *
        deltaWordFormula hn (sampledConstraintCircuit w r s) x y

 theorem constraintWordFormula_correct {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (x y : CodeBits n) :
    constraintWordFormula hn w x y=constraintCircuitMatrix w x y := by
  unfold constraintWordFormula
  simp_rw [deltaWordFormula_correct]
  exact recover_constraint_circuit w x y

 theorem nonempty_edges_positive {n : ℕ} (G : Complexity.MatrixGraph n) (h : orderedEdges G≠[]) : 0<n := by
  cases n with
  | zero => exact False.elim (h rfl)
  | succ n => omega

/-- The concrete finite WordEval formula for an ordinary binary-encoded source graph.
Edgeless and zero-vertex graphs are evaluated directly. Runtime compilation is a separate theorem. -/
def independentWordFormula {n : ℕ} (G : Complexity.MatrixGraph n) : ℚ :=
  if h:orderedEdges G=[] then (2:ℚ)^n else
    (independentSetProgram G).scalar * constraintWordFormula (nonempty_edges_positive G h)
      (independentSetProgram G).gates (zeroBits n) (zeroBits n)

/-- The full source→adjacent constraints→Δ→physical words chain preserves actual independent-set counts. -/
theorem independentWordFormula_correct {n : ℕ} (G : Complexity.MatrixGraph n) :
    independentWordFormula G=G.independentCount := by
  unfold independentWordFormula
  split_ifs with h
  · exact_mod_cast (independentCount_edgeless G h).symm
  · rw [constraintWordFormula_correct]
    exact independentSet_circuit_entry G

/-- Uniform bound on the actual Δ-circuit length at every spectral grid point. -/
def spectralCircuitSize (L : ℕ) : ℕ := (1+4*(L+1)^2)*L

/-- Every actual WordEval query in the composite spectral/conjugation grid has polynomial physical length. -/
theorem constraintWordQuery_length {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n))
    (r : Fin (Fintype.card (SpectralIndex (forbidOccurrences w))))
    (s : Fin (Fintype.card (SpectralIndex (signOccurrences w))))
    (u : Fin (2*deltaOccurrences (sampledConstraintCircuit w r.val s.val)+1)) (x y : CodeBits n) :
    (compileWordInstance hn ((sampledConstraintCircuit w r.val s.val).map (DeltaGate.compileSample u.val)) x y).word.length ≤
      (2624*spectralCircuitSize w.length+1640)*spectralCircuitSize w.length+
        (spectralCircuitSize w.length+2)*(40*n^3+40*n) := by
  have hs := sampledConstraintCircuit_grid_length w r s
  change (sampledConstraintCircuit w r.val s.val).length≤spectralCircuitSize w.length at hs
  have h := deltaQuery_word_length_nodes hn (sampledConstraintCircuit w r.val s.val) u x y
  apply h.trans
  exact Nat.add_le_add
    (Nat.mul_le_mul (by omega) hs)
    (Nat.mul_le_mul_right _ (by omega))

end
end HiddenCircuits.Circuit
