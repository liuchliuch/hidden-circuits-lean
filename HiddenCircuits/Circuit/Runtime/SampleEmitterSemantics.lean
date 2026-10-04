import HiddenCircuits.Circuit.Runtime.SampleEmitterDelta

namespace HiddenCircuits.Circuit.Runtime.SampleEmitter
open HiddenCircuits.Complexity

lemma encode_word_flatMap {α : Type*} {n : ℕ} (xs : List α) (f : α → List (Letter n)) :
    encodeBitList ((xs.flatMap f).map letterBits)=xs.flatMap (fun a => encodeBitList ((f a).map letterBits)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.map_append,BinaryArithmetic.encodeBitList_append,ih]

def gateOutput {n : ℕ} (a : ConstraintGate n) (r s u : ℕ) : BitString :=
  encodeBitList ((compileProjected ((a.sampleWord r s).map (DeltaGate.compileSample u))).word.map letterBits)
def gateExponent {n : ℕ} (a : ConstraintGate n) (r s u : ℕ) : ℕ :=
  ((a.sampleWord r s).map (fun d => SampleScalar.deltaExponent u d+SampleScalar.projectionExponent n)).sum
def gateNegative {n : ℕ} (a : ConstraintGate n) (negative : Bool) : Bool :=
  match a with | .one _ a => SampleLocalEmitter.oneNegative a negative | _ => negative

def sampleOutput {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) : BitString :=
  encodeBitList ((compileProjected ((sampledConstraintCircuit w r s).map (DeltaGate.compileSample u))).word.map letterBits)
def sampleGain {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) : ℕ :=
  (w.map (fun a => gateExponent a r s u)).sum
def sampleNegative {n : ℕ} (w : List (ConstraintGate n)) (negative : Bool) : Bool :=
  w.foldl (fun b a => gateNegative a b) negative

theorem gateOutput_flatMap {n : ℕ} (a : ConstraintGate n) (r s u : ℕ) :
    gateOutput a r s u=(a.sampleWord r s).flatMap (fun d => deltaBytes (d.compileSample u)) := by
  rw [gateOutput,SampleLocalEmitter.compileProjected_word,List.flatMap_map,encode_word_flatMap]
  rfl

theorem gateOutput_one {n : ℕ} (p : Placement n 1) (a : OneGate) (r s u : ℕ) :
    gateOutput (.one p a) r s u=deltaBytes (placedOneGateWord p a) := by
  simp only [gateOutput_flatMap,ConstraintGate.sampleWord,List.flatMap_cons,List.flatMap_nil,List.append_nil,DeltaGate.compileSample]
theorem gateOutput_forbid {n : ℕ} (p : Placement n 2) (r s u : ℕ) :
    gateOutput (.forbid p) r s u=(List.replicate (2*r) (deltaBytes ((sampleGWord u).lift p))).flatten := by
  simp [gateOutput_flatMap,ConstraintGate.sampleWord,List.flatMap_replicate,DeltaGate.compileSample]
theorem gateOutput_controlledSign {n : ℕ} (p : Placement n 2) (r s u : ℕ) :
    gateOutput (.controlledSign p) r s u=(List.replicate (2*s) (deltaBytes ((sampleGWord u).lift p))).flatten := by
  simp [gateOutput_flatMap,ConstraintGate.sampleWord,List.flatMap_replicate,DeltaGate.compileSample]

theorem gateExponent_one {n : ℕ} (p : Placement n 1) (a : OneGate) (r s u : ℕ) :
    gateExponent (.one p a) r s u=SampleScalar.oneExponent a+SampleScalar.projectionExponent n := by
  simp [gateExponent,ConstraintGate.sampleWord,SampleScalar.deltaExponent]
theorem gateExponent_forbid {n : ℕ} (p : Placement n 2) (r s u : ℕ) :
    gateExponent (.forbid p) r s u=2*r*(290*u+372+SampleScalar.projectionExponent n) := by
  simp [gateExponent,ConstraintGate.sampleWord,SampleScalar.deltaExponent]
theorem gateExponent_controlledSign {n : ℕ} (p : Placement n 2) (r s u : ℕ) :
    gateExponent (.controlledSign p) r s u=2*s*(290*u+372+SampleScalar.projectionExponent n) := by
  simp [gateExponent,ConstraintGate.sampleWord,SampleScalar.deltaExponent]

@[simp] theorem sampleOutput_nil (n r s u : ℕ) : sampleOutput (n:=n) [] r s u=[] := rfl
@[simp] theorem sampleOutput_cons {n : ℕ} (a : ConstraintGate n) (w : List (ConstraintGate n)) (r s u : ℕ) :
    sampleOutput (a::w) r s u=gateOutput a r s u++sampleOutput w r s u := by
  simp only [sampleOutput,gateOutput,SampleLocalEmitter.compileProjected_word,encode_word_flatMap,
    sampledConstraintCircuit,List.flatMap_cons,List.map_append,List.flatMap_append,BinaryArithmetic.encodeBitList_append]

lemma sampleGain_delta {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    sampleGain w r s u=((sampledConstraintCircuit w r s).map
      (fun d => SampleScalar.deltaExponent u d+SampleScalar.projectionExponent n)).sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change gateExponent a r s u+sampleGain w r s u=_
    rw [ih]
    simp only [sampledConstraintCircuit,List.flatMap_cons,List.map_append,List.sum_append]
    rfl

lemma sampleGain_eq {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    2*SampleScalar.projectionExponent n+sampleGain w r s u=SampleScalar.sampleExponent w r s u := by
  have hsplit (ds : List (DeltaGate n)) :
      (ds.map (fun d => SampleScalar.deltaExponent u d+SampleScalar.projectionExponent n)).sum=
        (ds.map (SampleScalar.deltaExponent u)).sum+SampleScalar.projectionExponent n*ds.length := by
    induction ds with
    | nil => simp
    | cons d ds ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.mul_succ];omega
  rw [sampleGain_delta,hsplit,SampleScalar.sampled_exponent_sum,SampleScalar.sampled_length]
  unfold SampleScalar.sampleExponent
  ring

def signValue (negative : Bool) : ℚ := if negative then -1 else 1
lemma gateNegative_value {n : ℕ} (a : ConstraintGate n) (negative : Bool) :
    signValue (gateNegative a negative)=(-1:ℚ)^(SampleScalar.hadamardCount [a])*signValue negative := by
  cases a with
  | one p a => cases a <;> cases negative <;> norm_num [signValue,gateNegative,SampleLocalEmitter.oneNegative,SampleScalar.hadamardCount,SampleScalar.oneSign] <;> split_ifs <;> norm_num
  | forbid p => cases negative <;> norm_num [signValue,gateNegative,SampleLocalEmitter.oneNegative,SampleScalar.hadamardCount,SampleScalar.oneSign] <;> split_ifs <;> norm_num
  | controlledSign p => cases negative <;> norm_num [signValue,gateNegative,SampleLocalEmitter.oneNegative,SampleScalar.hadamardCount,SampleScalar.oneSign] <;> split_ifs <;> norm_num

lemma sampleNegative_value {n : ℕ} (w : List (ConstraintGate n)) (negative : Bool) :
    signValue (sampleNegative w negative)=(-1:ℚ)^(SampleScalar.hadamardCount w)*signValue negative := by
  induction w generalizing negative with
  | nil => simp [sampleNegative,SampleScalar.hadamardCount]
  | cons a w ih =>
    have hc : SampleScalar.hadamardCount (a::w)=SampleScalar.hadamardCount [a]+SampleScalar.hadamardCount w := by
      cases a <;> simp [SampleScalar.hadamardCount]
    change signValue (sampleNegative w (gateNegative a negative))=_
    rw [ih,gateNegative_value,hc,pow_add]
    ring

end HiddenCircuits.Circuit.Runtime.SampleEmitter
