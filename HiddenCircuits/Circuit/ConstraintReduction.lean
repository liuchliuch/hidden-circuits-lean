import HiddenCircuits.Circuit.DoubleSpectral
import HiddenCircuits.Circuit.SpectralPlacement
import HiddenCircuits.Circuit.SampleBounds

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- Actual adjacent-wire circuits over the one-bit basis and the N/CZ constraints. -/
inductive ConstraintGate (n : ℕ) where
  | one (p : Placement n 1) (g : OneGate)
  | forbid (p : Placement n 2)
  | controlledSign (p : Placement n 2)

def ConstraintGate.matrix {n : ℕ} : ConstraintGate n → Matrix (CodeBits n) (CodeBits n) ℚ
  | .one p g => p.lift g.logical
  | .forbid p => p.lift (logicalConstraint 0)
  | .controlledSign p => p.lift (logicalConstraint (-1))

def ConstraintGate.spectral {n : ℕ} : ConstraintGate n → BiSpectralGate (CodeBits n)
  | .one p g => .fixed (p.lift g.logical)
  | .forbid p => .first p.spectralClass
  | .controlledSign p => .second p.spectralClass

/-- Every occurrence of each target type uses the same parameter, even when interleaved. -/
def ConstraintGate.sampleWord {n : ℕ} (r s : ℕ) : ConstraintGate n → List (DeltaGate n)
  | .one p g => [.one p g]
  | .forbid p => List.replicate (2*r) (.constraint p)
  | .controlledSign p => List.replicate (2*s) (.constraint p)

def constraintCircuitMatrix {n : ℕ} (w : List (ConstraintGate n)) : Matrix (CodeBits n) (CodeBits n) ℚ :=
  (w.map ConstraintGate.matrix).prod

def sampledConstraintCircuit {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) : List (DeltaGate n) :=
  w.flatMap (ConstraintGate.sampleWord r s)

def forbidOccurrences {n : ℕ} (w : List (ConstraintGate n)) : ℕ := firstMarks (w.map ConstraintGate.spectral)
def signOccurrences {n : ℕ} (w : List (ConstraintGate n)) : ℕ := secondMarks (w.map ConstraintGate.spectral)

 theorem ConstraintGate.spectral_target {n : ℕ} (g : ConstraintGate n) :
    BiSpectralGate.target 0 (-1) g.spectral=g.matrix := by
  cases g with
  | one p g => rfl
  | forbid p => exact (placed_constraint_target p 0).symm
  | controlledSign p => exact (placed_constraint_target p (-1)).symm

 theorem ConstraintGate.sampleWord_matrix {n : ℕ} (g : ConstraintGate n) (r s : ℕ) :
    deltaCircuitMatrix (g.sampleWord r s)=BiSpectralGate.sample r s g.spectral := by
  cases g with
  | one p g => simp [sampleWord,deltaCircuitMatrix,DeltaGate.matrix,BiSpectralGate.sample,spectral]
  | forbid p =>
    change ((List.replicate (2*r) (DeltaGate.constraint p)).map DeltaGate.matrix).prod=_
    rw [List.map_replicate,List.prod_replicate]
    exact placed_delta_even_power p r
  | controlledSign p =>
    change ((List.replicate (2*s) (DeltaGate.constraint p)).map DeltaGate.matrix).prod=_
    rw [List.map_replicate,List.prod_replicate]
    exact placed_delta_even_power p s

 theorem deltaCircuitMatrix_append {n : ℕ} (u v : List (DeltaGate n)) :
    deltaCircuitMatrix (u++v)=deltaCircuitMatrix u * deltaCircuitMatrix v := by
  simp [deltaCircuitMatrix]

/-- The emitted sample is a literal circuit containing only available one-bit gates and repeated Δ. -/
theorem sampledConstraintCircuit_matrix {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    deltaCircuitMatrix (sampledConstraintCircuit w r s)=
      ((w.map ConstraintGate.spectral).map (BiSpectralGate.sample r s)).prod := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    change deltaCircuitMatrix (g.sampleWord r s ++ sampledConstraintCircuit w r s)=_
    rw [deltaCircuitMatrix_append,ConstraintGate.sampleWord_matrix,ih]
    rfl

/-- Both target types are restored at once from the actual polynomial-sized rectangular sample grid. -/
theorem recover_constraint_circuit {n : ℕ} (w : List (ConstraintGate n)) (x y : CodeBits n) :
    (∑ r ∈ Finset.range (Fintype.card (SpectralIndex (forbidOccurrences w))),
      ∑ s ∈ Finset.range (Fintype.card (SpectralIndex (signOccurrences w))),
        targetCoefficient (forbidOccurrences w) 0 r * targetCoefficient (signOccurrences w) (-1) s *
          deltaCircuitMatrix (sampledConstraintCircuit w r s) x y) = constraintCircuitMatrix w x y := by
  have h := double_spectral_circuit_recovery (w.map ConstraintGate.spectral) 0 (-1) x y
  simp_rw [← sampledConstraintCircuit_matrix] at h
  simpa only [forbidOccurrences,signOccurrences,List.map_map,
    Function.comp_def,ConstraintGate.spectral_target,constraintCircuitMatrix] using h

 theorem constraintOccurrences_le_length {n : ℕ} (w : List (ConstraintGate n)) :
    forbidOccurrences w≤w.length ∧ signOccurrences w≤w.length := by
  induction w with
  | nil => simp [forbidOccurrences,signOccurrences,firstMarks,secondMarks]
  | cons g w ih =>
    cases g <;> simp only [forbidOccurrences,signOccurrences,List.map_cons,ConstraintGate.spectral,
      firstMarks,secondMarks,List.length_cons] at * <;> omega

 theorem sampledConstraintCircuit_length {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    (sampledConstraintCircuit w r s).length≤(1+2*r+2*s)*w.length := by
  induction w with
  | nil => simp [sampledConstraintCircuit]
  | cons g w ih =>
    change (g.sampleWord r s ++ sampledConstraintCircuit w r s).length≤_
    rw [List.length_append]
    have hg : (g.sampleWord r s).length≤1+2*r+2*s := by
      cases g <;> simp [ConstraintGate.sampleWord] <;> omega
    simp only [List.length_cons]
    nlinarith

/-- Explicit polynomial query-circuit size on the actual finite spectral grid. -/
theorem sampledConstraintCircuit_grid_length {n : ℕ} (w : List (ConstraintGate n))
    (r : Fin (Fintype.card (SpectralIndex (forbidOccurrences w))))
    (s : Fin (Fintype.card (SpectralIndex (signOccurrences w)))) :
    (sampledConstraintCircuit w r.val s.val).length≤(1+4*(w.length+1)^2)*w.length := by
  have hr := (Nat.le_of_lt r.isLt).trans (spectralIndex_card_bound _)
  have hs := (Nat.le_of_lt s.isLt).trans (spectralIndex_card_bound _)
  have hc := constraintOccurrences_le_length w
  have h1 := Nat.pow_le_pow_left (Nat.add_le_add_right hc.1 1) 2
  have h2 := Nat.pow_le_pow_left (Nat.add_le_add_right hc.2 1) 2
  exact (sampledConstraintCircuit_length w r.val s.val).trans
    (Nat.mul_le_mul_right w.length (by omega))

 theorem constraintQuery_grid_card {n : ℕ} (w : List (ConstraintGate n)) :
    Fintype.card (Fin (Fintype.card (SpectralIndex (forbidOccurrences w))) ×
      Fin (Fintype.card (SpectralIndex (signOccurrences w)))) =
    ((forbidOccurrences w+1)*(forbidOccurrences w+2)/2) *
      ((signOccurrences w+1)*(signOccurrences w+2)/2) := by
  simp only [Fintype.card_prod,Fintype.card_fin,spectralIndex_card]

end HiddenCircuits.Circuit
