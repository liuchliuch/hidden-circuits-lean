import HiddenCircuits.Circuit.Runtime.ConstraintSourceIdentity
import HiddenCircuits.Complexity.OracleRepeat
import HiddenCircuits.Complexity.PairSerialization

namespace HiddenCircuits.Circuit.Runtime.ConstraintSource
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

def zeroPairMap : Fin 3 ↪ Fin 36 := ⟨fun i=>![0,5,7] i,by decide +kernel⟩
noncomputable def zeroPair : OracleBlock 35 := seq (copyOn 2 6 7 (by decide) (by decide) (by decide))
  (seq (repeatPrepend 6 5 [false]) (PairSerialization.on zeroPairMap))
noncomputable def prepareQuery : OracleBlock 35 := seq zeroPair zeroPair
lemma zero_mask (n : ℕ) : BoundaryTransport.mask n (zeroBits n)=List.replicate n false := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp [BoundaryTransport.mask,zeroBits,ih,List.replicate_succ]
lemma query_encode {n : ℕ} (G : MatrixGraph n) : (query G).encode=
    pairBits (List.replicate n false) (pairBits (List.replicate n false) (circuitBits n (restoringIndependentProgram G).gates)) := by
  simp [query,ConstraintInput.encode,BoundaryTransport.inputBits,zero_mask]

def queryStore (raw : BitString) (a n f z : ℕ) (mask clock : BitString := []) : Store 35 := fun i=>
  if i.val=0 then raw else if i.val=1 then List.replicate a true else if i.val=2 then List.replicate n true
  else if i.val=3 then List.replicate f true else if i.val=4 then List.replicate z true
  else if i.val=5 then mask else if i.val=6 then clock else []
lemma queryStore_eq (raw : BitString) (a n f z : ℕ) : queryStore raw a n f z=SourceMetadata.outputStore raw a n f z := by
  funext i;fin_cases i <;> rfl
lemma zeroPair_executes (g : BitString→ℕ) (raw : BitString) (a n f z : ℕ) :
    zeroPair.Executes g (queryStore raw a n f z) (queryStore (pairBits (List.replicate n false) raw) a n f z) (21*n+16) := by
  have hc : (copyOn (2:Fin 36) 6 7 (by decide) (by decide) (by decide)).Executes g
      (queryStore raw a n f z) (queryStore raw a n f z [] (List.replicate n true)) (5*n+2) := by
    convert copyOn_executes g (2:Fin 36) 6 7 (by decide) (by decide) (by decide) (queryStore raw a n f z) rfl using 1
    · funext i;fin_cases i <;> simp [queryStore]
    · simp [queryStore]
  have hr : (repeatPrepend (6:Fin 36) 5 [false]).Executes g
      (queryStore raw a n f z [] (List.replicate n true)) (queryStore raw a n f z (List.replicate n false)) (6*n+1) := by
    convert repeatPrepend_executes g (6:Fin 36) 5 (by decide) [false]
      (queryStore raw a n f z [] (List.replicate n true)) using 1
    · funext i;fin_cases i <;> simp [queryStore,List.flatten_replicate_replicate]
    · simp [queryStore]
  have hp : (PairSerialization.on zeroPairMap).Executes g (queryStore raw a n f z (List.replicate n false))
      (queryStore (pairBits (List.replicate n false) raw) a n f z) (10*n+9) := by
    convert PairSerialization.on_executes zeroPairMap g (queryStore raw a n f z (List.replicate n false))
      (List.replicate n false) raw (by funext i;fin_cases i <;> rfl) using 1
    · funext i;fin_cases i <;> rfl
    · simp
  convert seq_executes _ _ g hc (seq_executes _ _ g hr hp) using 1 <;> omega
lemma prepareQuery_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixGraph n) :
    prepareQuery.Executes g (SourceMetadata.outputStore (circuitBits n (restoringIndependentProgram G).gates)
      (exponent G) n (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates))
      (SourceMetadata.outputStore (query G).encode (exponent G) n
        (forbidOccurrences (restoringIndependentProgram G).gates) (signOccurrences (restoringIndependentProgram G).gates)) (42*n+34) := by
  rw [query_encode,←queryStore_eq,←queryStore_eq]
  convert seq_executes _ _ g (zeroPair_executes g _ (exponent G) n _ _)
    (zeroPair_executes g _ (exponent G) n _ _) using 1 <;> omega
end HiddenCircuits.Circuit.Runtime.ConstraintSource
