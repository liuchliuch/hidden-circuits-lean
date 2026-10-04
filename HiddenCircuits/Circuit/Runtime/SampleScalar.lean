import HiddenCircuits.Circuit.ConstraintReduction
import HiddenCircuits.Circuit.SampleWords

/-! Exact signed dyadic normalization of the actual sampled physical word compiler. -/
namespace HiddenCircuits.Circuit.Runtime.SampleScalar
open scoped BigOperators

 def projectionExponent (n : ℕ) : ℕ := 6*n*globalProjectionExponent n
 def oneSign (g : OneGate) : ℕ := if g=.hadamard then 1 else 0
 def oneExponent (g : OneGate) : ℕ := if g=.swap then 3 else if g=.hadamard then 25 else 0

 theorem projectionScalar (n : ℕ) : (1/64:ℚ)^(n*globalProjectionExponent n)=(1/2:ℚ)^(projectionExponent n) := by
  have h : (1/64:ℚ)=(1/2:ℚ)^6 := by norm_num
  rw [h,←pow_mul]
  congr 1
  unfold projectionExponent
  ring

 theorem projectionExponent_eq (n : ℕ) : projectionExponent n=6*n*(2*n*(n-1)+2) := rfl

 theorem compileProjected_scalar {n : ℕ} (w : List (ScaledWord n)) :
    (compileProjected w).scalar=(w.map ScaledWord.scalar).prod*((1/2:ℚ)^(projectionExponent n))^w.length := by
  induction w with
  | nil => simp [compileProjected,ScaledWord.identity]
  | cons a w ih =>
    simp only [compileProjected,ScaledWord.compose,List.map_cons,List.prod_cons,List.length_cons,ih,projectionScalar,pow_succ]
    ring

 theorem oneGate_scalar (g : OneGate) : (oneGateWord g).scalar=(-1:ℚ)^(oneSign g)*(1/2:ℚ)^(oneExponent g) := by
  cases g <;> decide +kernel

 theorem local_sample_product (u : ℕ) :
    (((sampleLocalCircuit u).map AvailableGate.compile).map ScaledWord.scalar).prod=(1/2:ℚ)^12 := by
  norm_num [sampleLocalCircuit,AvailableGate.compile,placedOneGateWord,ScaledWord.lift,oneGateWord,twoGateWord]

 theorem sampleG_scalar (u : ℕ) : (sampleGWord u).scalar=(1/2:ℚ)^(290*u+372) := by
  change ((((2:ℚ)^u)⁻¹)^2)*(compileProjected ((sampleLocalCircuit u).map AvailableGate.compile)).scalar=_
  rw [compileProjected_scalar,local_sample_product,List.length_map,sampleLocalCircuit_length]
  have h : ((2:ℚ)^u)⁻¹=(1/2:ℚ)^u := by simp [one_div]
  rw [h]
  have he : projectionExponent 2=72 := rfl
  rw [he]
  have hu : ((1/2:ℚ)^u)^2=(1/2:ℚ)^(2*u) := by rw [←pow_mul,Nat.mul_comm]
  have hp : ((1/2:ℚ)^72)^(4*u+5)=(1/2:ℚ)^(72*(4*u+5)) := (pow_mul _ _ _).symm
  rw [hu,hp,←pow_add,←pow_add]
  exact congrArg (fun e : ℕ => (1/2:ℚ)^e) (by ring)

 def deltaSign {n : ℕ} : DeltaGate n → ℕ
  | .one _ g => oneSign g
  | .constraint _ => 0
 def deltaExponent {n : ℕ} (u : ℕ) : DeltaGate n → ℕ
  | .one _ g => oneExponent g
  | .constraint _ => 290*u+372

 theorem delta_scalar {n : ℕ} (u : ℕ) (g : DeltaGate n) :
    (g.compileSample u).scalar=(-1:ℚ)^(deltaSign g)*(1/2:ℚ)^(deltaExponent u g) := by
  cases g with
  | one p g => exact oneGate_scalar g
  | constraint p => simpa [deltaSign,deltaExponent,DeltaGate.compileSample,ScaledWord.lift] using sampleG_scalar u

 theorem delta_product {n : ℕ} (u : ℕ) (w : List (DeltaGate n)) :
    ((w.map (DeltaGate.compileSample u)).map ScaledWord.scalar).prod=
      (-1:ℚ)^((w.map deltaSign).sum)*(1/2:ℚ)^((w.map (deltaExponent u)).sum) := by
  induction w with
  | nil => simp
  | cons g w ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons,delta_scalar,ih,pow_add]
    ring

 theorem closed_delta_scalar {n : ℕ} (u : ℕ) (w : List (DeltaGate n)) :
    closedScalar (w.map (DeltaGate.compileSample u))=
      (-1:ℚ)^((w.map deltaSign).sum)*
        (1/2:ℚ)^(projectionExponent n*(w.length+2)+(w.map (deltaExponent u)).sum) := by
  unfold closedScalar
  rw [compileProjected_scalar,delta_product,List.length_map,projectionScalar]
  simp only [Nat.mul_add,pow_mul,pow_add]
  ring

 def oneCount {n : ℕ} : List (ConstraintGate n) → ℕ
  | [] => 0
  | .one _ _::w => 1+oneCount w
  | _::w => oneCount w
 def swapCount {n : ℕ} : List (ConstraintGate n) → ℕ
  | [] => 0
  | .one _ g::w => (if g=.swap then 1 else 0)+swapCount w
  | _::w => swapCount w
 def hadamardCount {n : ℕ} : List (ConstraintGate n) → ℕ
  | [] => 0
  | .one _ g::w => oneSign g+hadamardCount w
  | _::w => hadamardCount w
 def constraintCopies {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) : ℕ :=
  2*r*forbidOccurrences w+2*s*signOccurrences w

 theorem oneExponent_eq (g : OneGate) : oneExponent g=3*(if g=.swap then 1 else 0)+25*oneSign g := by
  cases g <;> decide +kernel

 theorem sampled_sign_sum {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    ((sampledConstraintCircuit w r s).map deltaSign).sum=hadamardCount w := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g <;> simp_all [sampledConstraintCircuit,ConstraintGate.sampleWord,hadamardCount,deltaSign]

 theorem sampled_length {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    (sampledConstraintCircuit w r s).length=oneCount w+constraintCopies w r s := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g <;> simp_all [sampledConstraintCircuit,ConstraintGate.sampleWord,oneCount,constraintCopies,
      forbidOccurrences,signOccurrences,ConstraintGate.spectral,firstMarks,secondMarks]
    all_goals ring

 theorem sampled_exponent_sum {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    ((sampledConstraintCircuit w r s).map (deltaExponent u)).sum=
      3*swapCount w+25*hadamardCount w+constraintCopies w r s*(290*u+372) := by
  induction w with
  | nil => simp [sampledConstraintCircuit,swapCount,hadamardCount,constraintCopies,forbidOccurrences,signOccurrences,firstMarks,secondMarks]
  | cons g w ih =>
    cases g <;> simp_all [sampledConstraintCircuit,ConstraintGate.sampleWord,deltaExponent,swapCount,hadamardCount,
      oneExponent_eq,constraintCopies,forbidOccurrences,signOccurrences,ConstraintGate.spectral,firstMarks,secondMarks]
    all_goals first | (split_ifs <;> ring) | ring

 def sampleExponent {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) : ℕ :=
  projectionExponent n*(oneCount w+constraintCopies w r s+2)+3*swapCount w+25*hadamardCount w+
    constraintCopies w r s*(290*u+372)

/-- Exact scalar attached to the actual physical WordInstance sample. -/
theorem sampled_closedScalar {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    closedScalar ((sampledConstraintCircuit w r s).map (DeltaGate.compileSample u))=
      (-1:ℚ)^(hadamardCount w)*(1/2:ℚ)^(sampleExponent w r s u) := by
  rw [closed_delta_scalar,sampled_sign_sum,sampled_length,sampled_exponent_sum]
  unfold sampleExponent
  congr 1
  congr 1
  omega

theorem sampled_closedScalar_div {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    closedScalar ((sampledConstraintCircuit w r s).map (DeltaGate.compileSample u))=
      (-1:ℚ)^(hadamardCount w)/(2:ℚ)^(sampleExponent w r s u) := by
  rw [sampled_closedScalar]
  simp [one_div,inv_pow,div_eq_mul_inv]

theorem sampled_closedScalar_ne_zero {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    closedScalar ((sampledConstraintCircuit w r s).map (DeltaGate.compileSample u))≠0 := by
  rw [sampled_closedScalar_div]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

end HiddenCircuits.Circuit.Runtime.SampleScalar
