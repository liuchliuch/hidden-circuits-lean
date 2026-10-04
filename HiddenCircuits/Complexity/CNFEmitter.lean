import HiddenCircuits.Complexity.CNFSerialization
import HiddenCircuits.Complexity.OracleRepeat

/-! Actual finite-instruction serializers for the concrete CNF bit encoding.
The output stack is a reversed stream; one final verified reversal produces the
canonical input. Unary indices are consumed one bit at a time, with exact costs. -/
namespace HiddenCircuits.Complexity.CNFEmitter
open OracleBlock
variable {k : ℕ}

/-- Serialize a unary variable count into the reversed formula header. -/
noncomputable def header (counter output : Fin (k+1)) : OracleBlock k :=
  seq (repeatPrepend counter output [true,true]) (push output false)

theorem header_executes (g : BitString → ℕ) (counter output : Fin (k+1))
    (hne : counter ≠ output) (s : Store k) :
    (header counter output).Executes g s
      (Function.update (Function.update s counter []) output
        (false::(List.replicate (2*(s counter).length) true++s output)))
      (9*(s counter).length+4) := by
  have hloop := repeatPrepend_executes g counter output hne [true,true] s
  have hpush := push_executes g output false
    (Function.update (Function.update s counter []) output
      ((List.replicate (s counter).length [true,true]).flatten++s output))
  have h := seq_executes _ _ g hloop hpush
  rw [show [true,true] = List.replicate 2 true from rfl] at h
  simp only [List.flatten_replicate_replicate] at h
  convert h using 1 <;> simp [Nat.mul_comm] <;> ring

lemma header_queryFree (counter output : Fin (k+1)) : (header counter output).QueryFree :=
  seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (push_queryFree _ _)

def literalTail (sign : Bool) : BitString := [false,true,true,true,sign,true,false]

/-- Emit a complete literal chunk, including its nested list delimiters. -/
noncomputable def literal (counter output : Fin (k+1)) (sign : Bool) : OracleBlock k :=
  seq (prepend output (List.replicate 5 true))
    (seq (repeatPrepend counter output (List.replicate 8 true)) (prepend output (literalTail sign).reverse))

theorem literal_executes (g : BitString → ℕ) (counter output : Fin (k+1))
    (hne : counter ≠ output) (sign : Bool) (s : Store k) :
    (literal counter output sign).Executes g s
      (Function.update (Function.update s counter []) output
        ((serializedLiteral (s counter).length sign).reverse++s output))
      (27*(s counter).length+43) := by
  let s₁ := Function.update s output (List.replicate 5 true++s output)
  have h₁ := prepend_executes g output (List.replicate 5 true) s
  have h₂ := repeatPrepend_executes g counter output hne (List.replicate 8 true) s₁
  let s₂ := Function.update (Function.update s₁ counter []) output
    ((List.replicate (s₁ counter).length (List.replicate 8 true)).flatten++s₁ output)
  have h₃ := prepend_executes g output (literalTail sign).reverse s₂
  have h := seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃)
  dsimp only [s₂,s₁] at h
  simp only [List.flatten_replicate_replicate] at h
  convert h using 1
  · simp only [serializedLiteral,List.reverse_append,List.reverse_replicate,Function.update_self,
      Function.update_idem,Function.update_of_ne hne,Function.update_comm (Ne.symm hne),
      List.append_assoc,literalTail]
    rw [show 8*(s counter).length+5=(s counter).length*8+5 by omega,List.replicate_add]
    simp [List.append_assoc]
  · simp [hne,literalTail];ring

lemma literal_queryFree (counter output : Fin (k+1)) (sign : Bool) :
    (literal counter output sign).QueryFree :=
  seq_queryFree _ _ (prepend_queryFree _ _) (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (prepend_queryFree _ _))

/-- Clause boundaries are individual actual pushes, outside the literal chunks. -/
def clauseStart (output : Fin (k+1)) : OracleBlock k := push output true
def clauseEnd (output : Fin (k+1)) : OracleBlock k := push output false

theorem clauseStart_executes (g : BitString → ℕ) (output : Fin (k+1)) (s : Store k) :
    (clauseStart output).Executes g s (Function.update s output (true::s output)) 1 := push_executes g output true s

theorem clauseEnd_executes (g : BitString → ℕ) (output : Fin (k+1)) (s : Store k) :
    (clauseEnd output).Executes g s (Function.update s output (false::s output)) 1 := push_executes g output false s

end HiddenCircuits.Complexity.CNFEmitter
