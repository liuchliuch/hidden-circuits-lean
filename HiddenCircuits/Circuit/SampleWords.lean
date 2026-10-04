import HiddenCircuits.Circuit.AvailableWords
import HiddenCircuits.Circuit.Conjugation

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- Whole-pair placement of G inside the isolated two-bit circuit. -/
def fullTwoBits : Placement 2 2 := ⟨0,0,rfl⟩

 theorem fullTwoBits_G_basis : (fullTwoBits.lift logicalG).submatrix twoBitEquiv twoBitEquiv=G := by
  decide +kernel

/-- The concrete4u+5-gate circuit implementing one conjugated G sample. -/
def sampleLocalCircuit (u : ℕ) : List (AvailableGate 2) :=
  List.replicate u (.one firstBit .scale) ++
  List.replicate u (.one secondBit .scale) ++
  [.interaction fullTwoBits,.one firstBit .swap] ++
  List.replicate u (.one firstBit .scale) ++
  [.one firstBit .swap,.one secondBit .swap] ++
  List.replicate u (.one secondBit .scale) ++ [.one secondBit .swap]

 theorem sampleLocalCircuit_length (u : ℕ) : (sampleLocalCircuit u).length=4*u+5 := by
  simp [sampleLocalCircuit]
  omega

 theorem reindex_list_prod {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ≃ ι) (w : List (Matrix ι ι ℚ)) :
    w.prod.submatrix e e=(w.map (fun M => M.submatrix e e)).prod := by
  induction w with
  | nil =>
    ext i j
    simp [Matrix.one_apply,e.injective.eq_iff]
  | cons A w ih =>
    rw [List.prod_cons,Matrix.submatrix_mul _ _ _ _ _ e.bijective,ih,List.map_cons,List.prod_cons]

 theorem sampleLocalCircuit_basis (u : ℕ) :
    (availableCircuitMatrix (sampleLocalCircuit u)).submatrix twoBitEquiv twoBitEquiv =
      scaleFirst^u * scaleSecond^u * G * swapFirst * scaleFirst^u * swapFirst *
        swapSecond * scaleSecond^u * swapSecond := by
  rw [availableCircuitMatrix,reindex_list_prod]
  simp only [sampleLocalCircuit,List.map_append,List.map_replicate,List.map_cons,List.map_nil,
    List.prod_append,List.prod_replicate,List.prod_cons,List.prod_nil,AvailableGate.matrix,
    first_scale_basis,second_scale_basis,first_swap_basis,second_swap_basis,fullTwoBits_G_basis,mul_one]
  simp only [Matrix.mul_assoc]

/-- Actual elementary word implementing the shared conjugated G, including all projection factors. -/
def sampleGWord (u : ℕ) : ScaledWord 2 :=
  (compileProjected ((sampleLocalCircuit u).map AvailableGate.compile)).rescale ((((2:ℚ)^u)⁻¹)^2)

 theorem sampleGWord_matrix (u : ℕ) :
    (sampleGWord u).matrix = evaluateMatrix ((2:ℚ)^u) logicalGPolynomial := by
  have hprod : (((sampleLocalCircuit u).map AvailableGate.compile).map ScaledWord.matrix).prod =
      availableCircuitMatrix (sampleLocalCircuit u) := by
    simp only [List.map_map,Function.comp_def,AvailableGate.compile_matrix,availableCircuitMatrix]
  have hb : (sampleGWord u).matrix.submatrix twoBitEquiv twoBitEquiv =
      evaluateMatrix ((2:ℚ)^u) GPolynomial := by
    rw [sampleGWord,ScaledWord.rescale_matrix,compileProjected_matrix,hprod]
    change (((((2:ℚ)^u)⁻¹)^2) •
      (availableCircuitMatrix (sampleLocalCircuit u)).submatrix twoBitEquiv twoBitEquiv) = _
    rw [sampleLocalCircuit_basis]
    exact (sampledG_available_product u).symm
  ext x y
  obtain ⟨a,rfl⟩ := twoBitEquiv.surjective x
  obtain ⟨b,rfl⟩ := twoBitEquiv.surjective y
  simpa [evaluateMatrix,logicalGPolynomial] using congrFun (congrFun hb a) b

/-- Compile every sampled gate to its exact physical word on the requested adjacent region. -/
def DeltaGate.compileSample {n : ℕ} (u : ℕ) : DeltaGate n → ScaledWord n
  | .one p g => placedOneGateWord p g
  | .constraint p => (sampleGWord u).lift p

 theorem DeltaGate.compileSample_matrix {n : ℕ} (u : ℕ) (g : DeltaGate n) :
    (g.compileSample u).matrix=g.sample u := by
  cases g with
  | one p g => exact placedOneGateWord_matrix p g
  | constraint p =>
    rw [compileSample,ScaledWord.lift_matrix,sampleGWord_matrix,← evaluate_lift]
    exact DeltaGate.polynomial_sample u (.constraint p)

/-- Each nonnegative sample is one explicit WordEval query with correct scalar postprocessing. -/
theorem sampledDeltaCircuit_word {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : ℕ) (x y : CodeBits n) :
    sampledDeltaCircuit w u x y = closedScalar (w.map (DeltaGate.compileSample u)) *
      (compileWordInstance hn (w.map (DeltaGate.compileSample u)) x y).value := by
  have h := compileWordInstance_correct hn (w.map (DeltaGate.compileSample u)) x y
  simpa only [List.map_map,Function.comp_def,DeltaGate.compileSample_matrix,sampledDeltaCircuit] using h

/-- The mathematical oracle identity of Lemma7.1, with actual explicitly emitted WordInstances. -/
theorem deltaCircuit_from_word_queries {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (x y : CodeBits n) :
    (geometricInterpolate (2*deltaOccurrences w)
      (fun u => closedScalar (w.map (DeltaGate.compileSample u.val)) *
        (compileWordInstance hn (w.map (DeltaGate.compileSample u.val)) x y).value)).eval 0 =
      deltaCircuitMatrix w x y := by
  have h := recover_deltaCircuit w x y
  simpa only [sampledDeltaCircuit_word hn] using h

end HiddenCircuits.Circuit
