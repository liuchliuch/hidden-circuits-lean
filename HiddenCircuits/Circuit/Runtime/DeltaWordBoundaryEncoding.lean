import HiddenCircuits.Circuit.Runtime.DeltaWordBoundary
import HiddenCircuits.Circuit.Runtime.BoundaryPreprocessFinish

/-! Exact native Delta input bytes and the actual eight-stack mask/X-gate
preprocessor, including zero wires. No semantic identification of Delta with
its serialization descriptor is used. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaBoundary
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic

/-- The outer masks, width header and Delta gate stream are the native encoding. -/
def inputBits {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) : BitString :=
  BoundaryTransport.inputBits (w.map DeltaGate.descriptor) x y

lemma inputBits_eq_encode {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    inputBits w x y=(DeltaInput.mk n w x y).encode := rfl

lemma encode_eq_inputBits (C : DeltaInput) : C.encode=inputBits C.gates C.source C.target := rfl

lemma inputBits_zero (w : List (DeltaGate 0)) (x y : CodeBits 0) :
    inputBits w x y=[false,false,false] := by
  rw [gates_nil w]
  cases x;cases y
  rfl

lemma inputBits_succ (n : ℕ) (w : List (DeltaGate (n+1))) (x y : CodeBits (n+1)) :
    inputBits w x y=true::decide (x.1=1)::pairBits (BoundaryTransport.mask n x.2)
      (pairBits (BoundaryTransport.mask (n+1) y) (Runtime.circuitBits (n+1) (w.map DeltaGate.descriptor))) := rfl

lemma output_correct {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    BoundaryPreprocess.result (BoundaryTransport.mask n x) (BoundaryTransport.mask n y)
      (List.replicate n true) (encodeBitList ((w.map DeltaGate.descriptor).map Runtime.gateBits))=
        Runtime.circuitBits n ((zeroBoundaryCircuit w x y).map DeltaGate.descriptor) := by
  rw [zeroBoundaryCircuit_descriptor]
  exact BoundaryTransport.output_correct (w.map DeltaGate.descriptor) x y

/-- This is the existing finite physical byte program, with no circuit-valued
oracle or external preprocessing certificate. -/
noncomputable def preprocess : OracleBlock 7 := BoundaryPreprocess.program
noncomputable def preprocessTime := BoundaryPreprocess.time

def initial (raw : BitString) : Store 7 := Function.update (fun _=>[]) 0 raw

lemma initial_eq_store (raw : BitString) :
    initial raw=BoundaryPreprocess.store raw [] [] [] [] := by
  funext i;fin_cases i <;> rfl

lemma preprocess_executes (g : BitString→ℕ) {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    ∃c,preprocess.Executes g (initial (inputBits w x y))
      (initial (Runtime.circuitBits n ((zeroBoundaryCircuit w x y).map DeltaGate.descriptor))) c ∧
      c ≤ preprocessTime.eval (inputBits w x y).length := by
  obtain ⟨c,hc,hb⟩:=BoundaryPreprocess.program_executes g (BoundaryTransport.mask n x)
    (BoundaryTransport.mask n y) (List.replicate n true)
    (encodeBitList ((w.map DeltaGate.descriptor).map Runtime.gateBits))
  rw [output_correct] at hc
  refine ⟨c,?_,hb⟩
  simpa only [preprocess,initial_eq_store] using hc

lemma preprocess_queryFree : preprocess.QueryFree := BoundaryPreprocess.program_queryFree

lemma preprocess_executes_native (g : BitString→ℕ) (C : DeltaInput) :
    ∃c,preprocess.Executes g (initial C.encode)
      (initial (Runtime.circuitBits C.wires
        ((zeroBoundaryCircuit C.gates C.source C.target).map DeltaGate.descriptor))) c ∧
      c ≤ preprocessTime.eval C.encode.length := by
  exact preprocess_executes g C.gates C.source C.target

lemma preprocess_executes_zero (g : BitString→ℕ) :
    ∃c,preprocess.Executes g (initial [false,false,false]) (initial [false]) c ∧
      c ≤ preprocessTime.eval 3 := by
  exact preprocess_executes g (n:=0) [] PUnit.unit PUnit.unit

end HiddenCircuits.Circuit.Runtime.DeltaBoundary
