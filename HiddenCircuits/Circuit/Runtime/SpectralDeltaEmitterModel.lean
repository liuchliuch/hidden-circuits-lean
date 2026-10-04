import HiddenCircuits.Complexity.DeltaEncoding
import HiddenCircuits.Circuit.Runtime.GateEmitter
import HiddenCircuits.Circuit.Runtime.SampleGateDispatch
import HiddenCircuits.Circuit.Runtime.SamplePairParser
import HiddenCircuits.Circuit.Runtime.ConstraintSourceQuery

/-! Literal logical Δ-circuit queries for the two-parameter spectral reduction.
The physical Word compiler is not used here: the target is the named Δ oracle. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
open Complexity OracleBlock BinaryArithmetic Polynomial

def descriptor {n : ℕ} (g : DeltaGate n) : ConstraintGate n := Complexity.DeltaGate.descriptor g
def query {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) : DeltaInput :=
  ⟨n,sampledConstraintCircuit w r s,zeroBits n,zeroBits n⟩
def gateOutput {n : ℕ} (a : ConstraintGate n) (r s : ℕ) : BitString :=
  encodeBitList (((a.sampleWord r s).map descriptor).map gateBits)
def output {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) : BitString :=
  encodeBitList (((sampledConstraintCircuit w r s).map descriptor).map gateBits)
lemma query_encode {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    (query w r s).encode=pairBits (List.replicate n false)
      (pairBits (List.replicate n false) (pairBits (List.replicate n true) (output w r s))) := by
  simp only [query,DeltaInput.encode,DeltaInput.descriptor,ConstraintInput.encode,BoundaryTransport.inputBits,
    ConstraintSource.zero_mask,circuitBits,output]
  rfl
lemma output_nil (n r s : ℕ) : output (n:=n) [] r s=[] := rfl
lemma output_cons {n : ℕ} (a : ConstraintGate n) (w : List (ConstraintGate n)) (r s : ℕ) :
    output (a::w) r s=gateOutput a r s++output w r s := by
  simp only [output,gateOutput,sampledConstraintCircuit,List.flatMap_cons,List.map_append,encodeBitList_append]
lemma gateOutput_one {n : ℕ} (p : Placement n 1) (g : OneGate) (r s : ℕ) :
    gateOutput (.one p g) r s=GateEmitter.chunk (gateTag (.one p g)) p.before := by
  rw [gateOutput]
  exact (GateEmitter.chunk_gate (.one p g)).symm
lemma gateOutput_forbid {n : ℕ} (p : Placement n 2) (r s : ℕ) :
    gateOutput (.forbid p) r s=(List.replicate (2*r) (GateEmitter.chunk .forbid p.before)).flatten := by
  simp only [gateOutput,ConstraintGate.sampleWord,List.map_replicate,descriptor,Complexity.DeltaGate.descriptor]
  rw [encodeBitList_eq_flatMap,List.flatMap_replicate]
  congr 2
  simpa only [encodeBitList, gateTag, gatePosition, pairBits_escape, List.append_nil] using (GateEmitter.chunk_gate (.forbid p)).symm
lemma gateOutput_sign {n : ℕ} (p : Placement n 2) (r s : ℕ) :
    gateOutput (.controlledSign p) r s=(List.replicate (2*s) (GateEmitter.chunk .forbid p.before)).flatten := by
  simp only [gateOutput,ConstraintGate.sampleWord,List.map_replicate,descriptor,Complexity.DeltaGate.descriptor]
  rw [encodeBitList_eq_flatMap,List.flatMap_replicate]
  congr 2
  simpa only [encodeBitList, gateTag, gatePosition, pairBits_escape, List.append_nil] using (GateEmitter.chunk_gate (.forbid p)).symm

def store (circuit : BitString) (r s n : ℕ) (out stream atom tag clock left right result : BitString) : Store 15 :=
  fun i=>if i.val=0 then circuit else if i.val=1 then List.replicate r true
    else if i.val=2 then List.replicate s true else if i.val=3 then List.replicate n true
    else if i.val=4 then out else if i.val=5 then stream else if i.val=6 then atom
    else if i.val=7 then tag else if i.val=9 then clock else if i.val=10 then left
    else if i.val=11 then right else if i.val=15 then result else []
def gateMap : Fin 4 ↪ Fin 16 := ⟨fun i=>![6,4,12,13] i,by decide +kernel⟩
def gateParse : Fin 4 ↪ Fin 16 := ⟨fun i=>![5,6,12,13] i,by decide +kernel⟩
def atomParse : Fin 4 ↪ Fin 16 := ⟨fun i=>![6,7,12,13] i,by decide +kernel⟩
def headerParse : Fin 4 ↪ Fin 16 := ⟨fun i=>![5,3,12,13] i,by decide +kernel⟩
noncomputable def atom (tag : GateTag) : OracleBlock 15 := rename (GateEmitter.atom tag) gateMap
noncomputable def copies (source : Fin 16) (hne : source≠9) (ht : source≠14) : OracleBlock 15 :=
  seq (copyOn source 9 14 hne ht (by decide))
    (seq (copyOn source 9 14 hne ht (by decide)) (whilePop 9 (atom .forbid) (atom .forbid)))
noncomputable def tagBody : GateTag→OracleBlock 15
  | .forbid=>copies 1 (by decide) (by decide)
  | .controlledSign=>copies 2 (by decide) (by decide)
  | tag=>atom tag
noncomputable def dispatch : OracleBlock 15 := SampleGateDispatch.block 7 tagBody
noncomputable def body : OracleBlock 15 := seq (SamplePairParser.on gateParse)
  (seq (SamplePairParser.on atomParse) (seq dispatch (clear 6)))
noncomputable def loop : OracleBlock 15 := whilePop 5 body body
noncomputable def setup : OracleBlock 15 := seq (copyOn 0 5 14 (by decide) (by decide) (by decide)) (SamplePairParser.on headerParse)
noncomputable def gateTime (n r s : ℕ) : ℕ := (2*(r+s)+1)*(14*n+70)+10*(r+s)+9
end HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
