import HiddenCircuits.Circuit.BoundaryTransport
import HiddenCircuits.Circuit.Runtime.GateEmitter
import HiddenCircuits.Complexity.PairSerialization

namespace HiddenCircuits.Circuit.Runtime.BoundaryTransport
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic

def mask : (n : ℕ)→CodeBits n→BitString
  | 0,_=>[]
  | n+1,x=>decide (x.1=1)::mask n x.2
@[simp] lemma mask_length (n : ℕ) (x : CodeBits n) : (mask n x).length=n := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp [mask,ih]
def chunks : BitString→ℕ→BitString
  | [],_=>[]
  | b::bs,i=>(if b then GateEmitter.chunk .swap i else [])++chunks bs (i+1)
def shifted {n : ℕ} (w : List (ConstraintGate n)) (p : ℕ) : BitString :=
  w.flatMap (fun g=>GateEmitter.chunk (gateTag g) (p+gatePosition g))
lemma shifted_zero {n : ℕ} (w : List (ConstraintGate n)) : shifted w 0=encodeBitList (w.map gateBits) := by
  simpa [shifted] using GateEmitter.chunks_eq w
lemma shifted_append {n : ℕ} (u v : List (ConstraintGate n)) (p : ℕ) :
    shifted (u++v) p=shifted u p++shifted v p := by simp [shifted]
lemma gateTag_lift {n r : ℕ} (p : Placement n r) (g : ConstraintGate r) : gateTag (g.place p)=gateTag g := by
  cases g with
  | one q g=>cases g <;> rfl
  | forbid q=>rfl
  | controlledSign q=>rfl
lemma gatePosition_lift {n r : ℕ} (p : Placement n r) (g : ConstraintGate r) :
    gatePosition (g.place p)=p.before+gatePosition g := by cases g <;> rfl
lemma shifted_lift {n r : ℕ} (q : Placement n r) (w : List (ConstraintGate r)) (p : ℕ) :
    shifted (w.map (fun g=>g.place q)) p=shifted w (p+q.before) := by
  simp only [shifted,List.flatMap_map,Function.comp_def,gateTag_lift,gatePosition_lift,Nat.add_assoc]
lemma chunks_boundary (n : ℕ) (x : CodeBits n) (p : ℕ) :
    chunks (mask n x) p=shifted (boundaryProgram n x).gates p := by
  induction n generalizing p with
  | zero=>rfl
  | succ n ih=>
    rcases x with ⟨i,x⟩
    simp only [mask,chunks,boundaryProgram,ConstraintProgram.compose,ConstraintProgram.lift,shifted_append,
      shifted_lift,tailPlacement,ih]
    fin_cases i <;> simp [ConstraintProgram.identity,shifted,gateTag,gatePosition,headPlacement]

def inputBits {n : ℕ} (w : List (ConstraintGate n)) (x y : CodeBits n) : BitString :=
  pairBits (mask n x) (pairBits (mask n y) (circuitBits n w))
lemma output_correct {n : ℕ} (w : List (ConstraintGate n)) (x y : CodeBits n) :
    pairBits (List.replicate n true) (chunks (mask n x) 0++encodeBitList (w.map gateBits)++chunks (mask n y) 0)=
      circuitBits n (zeroBoundaryCircuit w x y) := by
  simp only [chunks_boundary,shifted_zero,circuitBits,zeroBoundaryCircuit,List.map_append,
    encodeBitList_append]
end HiddenCircuits.Circuit.Runtime.BoundaryTransport
