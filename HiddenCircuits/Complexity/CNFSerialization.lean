import HiddenCircuits.Complexity.CNFEncoding

/-! Explicit serial bit templates for the uniform CNF emitter. Nested paired-list
encoding expands each unary variable index into exactly eight `true` bits per
unit; no dynamic finite-type enumeration appears in these templates. -/
namespace HiddenCircuits.Complexity

def escapeBits : BitString → BitString
  | [] => []
  | b::bs => true::b::escapeBits bs

@[simp] theorem escapeBits_append (x y : BitString) : escapeBits (x++y) = escapeBits x++escapeBits y := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [escapeBits,ih]

theorem pairBits_escape (x y : BitString) : pairBits x y = escapeBits x++false::y := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairBits,escapeBits,ih]

@[simp] theorem escapeBits_replicate_true (n : ℕ) :
    escapeBits (List.replicate n true) = List.replicate (2*n) true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,escapeBits,ih,show 2*(n+1)=2*n+2 by omega]

/-- Literal bitstream after both surrounding paired-list escape layers. -/
def serializedLiteral (index : ℕ) (sign : Bool) : BitString :=
  List.replicate (8*index+5) true ++ [false,true,true,true,sign,true,false]

/-- Explicit serialization of raw natural-number literals, including both clause
boundary markers. Index bounds are separately supplied by a well-formed CNF. -/
def serializedClause (c : List (ℕ × Bool)) : BitString :=
  true :: (c.flatMap (fun l => serializedLiteral l.1 l.2)) ++ [false]

def serializedCNF (varCount : ℕ) (clauses : List (List (ℕ × Bool))) : BitString :=
  List.replicate (2*varCount) true ++ false :: clauses.flatMap serializedClause

@[simp] theorem serializedLiteral_length (i : ℕ) (b : Bool) : (serializedLiteral i b).length = 8*i+12 := by
  simp [serializedLiteral]

lemma serializedLiteral_eq (i : ℕ) (b : Bool) :
    serializedLiteral i b =
      [true,true] ++ escapeBits (escapeBits (pairBits (List.replicate i true) [b])) ++ [true,false] := by
  rw [pairBits_escape,escapeBits_append,escapeBits_append,escapeBits_replicate_true,escapeBits_replicate_true]
  simp only [escapeBits_replicate_true]
  simp [serializedLiteral,escapeBits,List.append_assoc,
    show 2*(2*(2*i))=8*i by omega,
    show 8*i+5=2+(8*i+3) by omega,
    List.replicate_add]

lemma escape_encodeBitList (xs : List BitString) :
    escapeBits (encodeBitList xs) =
      xs.flatMap (fun x => [true,true] ++ escapeBits (escapeBits x) ++ [true,false]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [encodeBitList,pairBits_escape,escapeBits,ih,List.append_assoc]

lemma encodeBitList_eq_flatMap (xs : List BitString) :
    encodeBitList xs = xs.flatMap (fun x => true::escapeBits x++[false]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeBitList,pairBits_escape,ih,List.append_assoc]

namespace CNF
variable {n m : ℕ}

theorem serializedClause_eq (c : List (Fin n × Bool)) :
    serializedClause (c.map (fun l => (l.1.val,l.2))) = true::escapeBits (clauseBits c)++[false] := by
  simp only [serializedClause,clauseBits,escape_encodeBitList,List.flatMap_map]
  congr 2
  apply congrArg (fun f => c.flatMap f)
  funext l
  exact serializedLiteral_eq l.1.val l.2

/-- The explicit scalar-index stream is the project's exact binary CNF encoding,
not merely an isomorphic or abstract size representation. -/
theorem bits_eq_serialized (F : CNF n m) :
    F.bits = serializedCNF n ((List.ofFn F.clause).map (List.map (fun l => (l.1.val,l.2)))) := by
  simp only [bits,serializedCNF,pairBits_escape,escapeBits_replicate_true,encodeBitList_eq_flatMap,
    List.flatMap_map]
  congr 2
  apply congrArg (fun f => (List.ofFn F.clause).flatMap f)
  funext c
  exact (serializedClause_eq c).symm
end CNF

end HiddenCircuits.Complexity
