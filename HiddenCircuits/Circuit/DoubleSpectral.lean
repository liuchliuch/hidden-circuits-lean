import HiddenCircuits.Circuit.SpectralCircuit

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- Two independently marked diagonal types may occur in any order among fixed gates. -/
inductive BiSpectralGate (ι : Type*) where
  | fixed (M : Matrix ι ι ℚ)
  | first (classify : ι → Fin 3)
  | second (classify : ι → Fin 3)

def firstMarks {ι : Type*} : List (BiSpectralGate ι) → ℕ
  | [] => 0
  | .first _::w => firstMarks w+1
  | _::w => firstMarks w

def secondMarks {ι : Type*} : List (BiSpectralGate ι) → ℕ
  | [] => 0
  | .second _::w => secondMarks w+1
  | _::w => secondMarks w

section
variable {ι : Type*} [DecidableEq ι]

def BiSpectralGate.sample (r s : ℕ) : BiSpectralGate ι → Matrix ι ι ℚ
  | .fixed M => M
  | .first c => SpectralGate.sample r (.marked c)
  | .second c => SpectralGate.sample s (.marked c)

def BiSpectralGate.mixed (z : ℚ) (s : ℕ) : BiSpectralGate ι → Matrix ι ι ℚ
  | .fixed M => M
  | .first c => SpectralGate.target z (.marked c)
  | .second c => SpectralGate.sample s (.marked c)

def BiSpectralGate.target (z z' : ℚ) : BiSpectralGate ι → Matrix ι ι ℚ
  | .fixed M => M
  | .first c => SpectralGate.target z (.marked c)
  | .second c => SpectralGate.target z' (.marked c)

def BiSpectralGate.firstView (s : ℕ) : BiSpectralGate ι → SpectralGate ι
  | .fixed M => .fixed M
  | .first c => .marked c
  | .second c => .fixed (SpectralGate.sample s (.marked c))

def BiSpectralGate.secondView (z : ℚ) : BiSpectralGate ι → SpectralGate ι
  | .fixed M => .fixed M
  | .first c => .fixed (SpectralGate.target z (.marked c))
  | .second c => .marked c

 theorem firstView_marks (w : List (BiSpectralGate ι)) (s : ℕ) :
    markCount (w.map (BiSpectralGate.firstView s))=firstMarks w := by
  induction w with
  | nil => rfl
  | cons g w ih => cases g <;> simp [BiSpectralGate.firstView,markCount,firstMarks,ih]

 theorem secondView_marks (w : List (BiSpectralGate ι)) (z : ℚ) :
    markCount (w.map (BiSpectralGate.secondView z))=secondMarks w := by
  induction w with
  | nil => rfl
  | cons g w ih => cases g <;> simp [BiSpectralGate.secondView,markCount,secondMarks,ih]

 theorem firstView_sample (w : List (BiSpectralGate ι)) (r s : ℕ) :
    (w.map (BiSpectralGate.firstView s)).map (SpectralGate.sample r)=w.map (BiSpectralGate.sample r s) := by
  induction w with
  | nil => rfl
  | cons g w ih => cases g <;> simp [BiSpectralGate.firstView,SpectralGate.sample,BiSpectralGate.sample,ih]

 theorem firstView_target (w : List (BiSpectralGate ι)) (z : ℚ) (s : ℕ) :
    (w.map (BiSpectralGate.firstView s)).map (SpectralGate.target z)=w.map (BiSpectralGate.mixed z s) := by
  induction w with
  | nil => rfl
  | cons g w ih => cases g <;> simp [BiSpectralGate.firstView,SpectralGate.target,BiSpectralGate.mixed,ih]

 theorem secondView_sample (w : List (BiSpectralGate ι)) (z : ℚ) (s : ℕ) :
    (w.map (BiSpectralGate.secondView z)).map (SpectralGate.sample s)=w.map (BiSpectralGate.mixed z s) := by
  induction w with
  | nil => rfl
  | cons g w ih => cases g <;> simp [BiSpectralGate.secondView,SpectralGate.sample,BiSpectralGate.mixed,ih]

 theorem secondView_target (w : List (BiSpectralGate ι)) (z z' : ℚ) :
    (w.map (BiSpectralGate.secondView z)).map (SpectralGate.target z')=w.map (BiSpectralGate.target z z') := by
  induction w with
  | nil => rfl
  | cons g w ih => cases g <;> simp [BiSpectralGate.secondView,SpectralGate.target,BiSpectralGate.target,ih]

/-- The coefficient lists are independently constructed on the two genuine finite node sets. -/
noncomputable def targetCoefficient (g : ℕ) (z : ℚ) (r : ℕ) : ℚ :=
  spectralCoefficient g (fun x => z^(g-x.1.val-x.2.val)) r

variable [Fintype ι]

theorem spectral_circuit_recovery_coeff (w : List (SpectralGate ι)) (z : ℚ) (x y : ι) :
    (∑ r ∈ Finset.range (Fintype.card (SpectralIndex (markCount w))),
      targetCoefficient (markCount w) z r * (w.map (SpectralGate.sample r)).prod x y) =
      (w.map (SpectralGate.target z)).prod x y :=
  spectral_circuit_recovery w z x y

/-- Exact two-parameter recovery in a genuine interleaved matrix circuit.
No assumption about commutation or grouping of the gate positions is made. -/
theorem double_spectral_circuit_recovery (w : List (BiSpectralGate ι)) (z z' : ℚ) (x y : ι) :
    (∑ r ∈ Finset.range (Fintype.card (SpectralIndex (firstMarks w))),
      ∑ s ∈ Finset.range (Fintype.card (SpectralIndex (secondMarks w))),
        targetCoefficient (firstMarks w) z r * targetCoefficient (secondMarks w) z' s *
          (w.map (BiSpectralGate.sample r s)).prod x y) =
      (w.map (BiSpectralGate.target z z')).prod x y := by
  have h1 (s : ℕ) :
      (∑ r ∈ Finset.range (Fintype.card (SpectralIndex (firstMarks w))),
        targetCoefficient (firstMarks w) z r * (w.map (BiSpectralGate.sample r s)).prod x y) =
        (w.map (BiSpectralGate.mixed z s)).prod x y := by
    have h := spectral_circuit_recovery_coeff (w.map (BiSpectralGate.firstView s)) z x y
    simpa only [firstView_marks,firstView_sample,firstView_target] using h
  have h2 :
      (∑ s ∈ Finset.range (Fintype.card (SpectralIndex (secondMarks w))),
        targetCoefficient (secondMarks w) z' s * (w.map (BiSpectralGate.mixed z s)).prod x y) =
        (w.map (BiSpectralGate.target z z')).prod x y := by
    have h := spectral_circuit_recovery_coeff (w.map (BiSpectralGate.secondView z)) z' x y
    simpa only [secondView_marks,secondView_sample,secondView_target] using h
  rw [Finset.sum_comm]
  calc
    _ = ∑ s ∈ Finset.range (Fintype.card (SpectralIndex (secondMarks w))),
        targetCoefficient (secondMarks w) z' s *
          ∑ r ∈ Finset.range (Fintype.card (SpectralIndex (firstMarks w))),
            targetCoefficient (firstMarks w) z r * (w.map (BiSpectralGate.sample r s)).prod x y := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by simp_rw [h1]; exact h2

end
end HiddenCircuits.Circuit
