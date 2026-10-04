import HiddenCircuits.Complexity.DeltaEncoding
import HiddenCircuits.Circuit.Runtime.SampleEmitterRuntime
import HiddenCircuits.Circuit.GeometricIntegerWeights

/-! The independent Delta-to-Word compiler uses one physical sample for every
Delta gate. In particular its constraint dispatch never repeats a source N/CZ
sample word. The two preserved r/s ports are unused by this compiler. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaWordEmitter
open HiddenCircuits.Complexity SampleEmitter

def gateBits {n : ℕ} (a : DeltaGate n) : BitString := Runtime.gateBits (DeltaGate.descriptor a)
def gateTag {n : ℕ} (a : DeltaGate n) : GateTag := Runtime.gateTag (DeltaGate.descriptor a)
def gatePosition {n : ℕ} (a : DeltaGate n) : ℕ := Runtime.gatePosition (DeltaGate.descriptor a)
def circuitBits (n : ℕ) (w : List (DeltaGate n)) : BitString := Runtime.circuitBits n (w.map DeltaGate.descriptor)
lemma circuitBits_eq (n : ℕ) (w : List (DeltaGate n)) :
    circuitBits n w=pairBits (List.replicate n true) (encodeBitList (w.map gateBits)) := by
  simp only [circuitBits,Runtime.circuitBits,List.map_map];rfl
lemma gateBits_length {n : ℕ} (a : DeltaGate n) : (gateBits a).length=gatePosition a+9 := Runtime.gateBits_length (DeltaGate.descriptor a)
lemma gatePosition_bound {n : ℕ} (a : DeltaGate n) : gatePosition a+(gateTag a).width≤n := Runtime.gatePosition_bound (DeltaGate.descriptor a)

def gateOutput {n : ℕ} (a : DeltaGate n) (u : ℕ) : BitString := deltaBytes (a.compileSample u)
def gateExponent {n : ℕ} (a : DeltaGate n) (u : ℕ) : ℕ :=
  SampleScalar.deltaExponent u a+SampleScalar.projectionExponent n
def gateNegative {n : ℕ} (a : DeltaGate n) (negative : Bool) : Bool :=
  match a with | .one _ a => SampleLocalEmitter.oneNegative a negative | .constraint _ => negative

def sampleOutput {n : ℕ} (w : List (DeltaGate n)) (u : ℕ) : BitString :=
  encodeBitList ((compileProjected (w.map (DeltaGate.compileSample u))).word.map letterBits)
def sampleGain {n : ℕ} (w : List (DeltaGate n)) (u : ℕ) : ℕ := (w.map (fun a => gateExponent a u)).sum
def sampleNegative {n : ℕ} (w : List (DeltaGate n)) (negative : Bool) : Bool := w.foldl (fun b a => gateNegative a b) negative
def sampleExponent {n : ℕ} (w : List (DeltaGate n)) (u : ℕ) : ℕ :=
  SampleScalar.projectionExponent n*(w.length+2)+(w.map (SampleScalar.deltaExponent u)).sum

@[simp] lemma sampleOutput_nil (n u : ℕ) : sampleOutput (n:=n) [] u=[] := rfl
@[simp] lemma sampleOutput_cons {n : ℕ} (a : DeltaGate n) (w : List (DeltaGate n)) (u : ℕ) :
    sampleOutput (a::w) u=gateOutput a u++sampleOutput w u := by
  simp only [sampleOutput,gateOutput,SampleLocalEmitter.compileProjected_word,List.map_cons,List.flatMap_cons,
    List.map_append,BinaryArithmetic.encodeBitList_append,deltaBytes]

lemma sampleGain_eq {n : ℕ} (w : List (DeltaGate n)) (u : ℕ) :
    2*SampleScalar.projectionExponent n+sampleGain w u=sampleExponent w u := by
  have h : sampleGain w u=(w.map (SampleScalar.deltaExponent u)).sum+SampleScalar.projectionExponent n*w.length := by
    induction w with
    | nil=>simp [sampleGain]
    | cons a w ih=>simp only [sampleGain,List.map_cons,List.sum_cons,List.length_cons,gateExponent,Nat.mul_succ] at *;omega
  rw [h];unfold sampleExponent;ring

lemma gateNegative_value {n : ℕ} (a : DeltaGate n) (negative : Bool) :
    signValue (gateNegative a negative)=(-1:ℚ)^(SampleScalar.deltaSign a)*signValue negative := by
  cases a with
  | one p a=>cases a <;> cases negative <;> norm_num [signValue,gateNegative,SampleLocalEmitter.oneNegative,SampleScalar.deltaSign,SampleScalar.oneSign] <;> split_ifs <;> norm_num
  | constraint p=>cases negative <;> norm_num [signValue,gateNegative,SampleScalar.deltaSign]
lemma sampleNegative_value {n : ℕ} (w : List (DeltaGate n)) (negative : Bool) :
    signValue (sampleNegative w negative)=(-1:ℚ)^((w.map SampleScalar.deltaSign).sum)*signValue negative := by
  induction w generalizing negative with
  | nil=>simp [sampleNegative,signValue]
  | cons a w ih=>
    change signValue (sampleNegative w (gateNegative a negative))=_
    rw [ih,gateNegative_value,List.map_cons,List.sum_cons,pow_add];ring
lemma scalar_eq {n : ℕ} (w : List (DeltaGate n)) (u : ℕ) :
    closedScalar (w.map (DeltaGate.compileSample u))=signValue (sampleNegative w false)/(2:ℚ)^(sampleExponent w u) := by
  rw [SampleScalar.closed_delta_scalar,sampleNegative_value]
  simp [sampleExponent,signValue,one_div,inv_pow,div_eq_mul_inv]
end HiddenCircuits.Circuit.Runtime.DeltaWordEmitter
