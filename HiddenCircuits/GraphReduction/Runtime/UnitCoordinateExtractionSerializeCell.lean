import HiddenCircuits.GraphReduction.Runtime.UnarySignedRead
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionLabelRead
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! A physical unary coordinate word is parsed, converted to canonical signed
binary, and emitted into a reverse native self-delimiting stream. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def coreState (values : BitString) (D : ℕ) (out stream unary signed acc : BitString) : Store 8 := fun i=>
  if i.val=0 then values else if i.val=1 then List.replicate D true
  else if i.val=2 then out else if i.val=3 then stream else if i.val=4 then unary
  else if i.val=5 then signed else if i.val=8 then acc else []

def parseEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := ![3,4,6,7] i
  inj' := by decide +kernel
def convertEmbedding (denominator : Bool) : Fin 4 ↪ Fin 9 where
  toFun i := ![if denominator then 1 else 4,5,6,7] i
  inj' := by cases denominator <;> decide +kernel
def emitEmbedding : Fin 2 ↪ Fin 9 where
  toFun i := if i=0 then 5 else 8
  inj' := by decide +kernel
noncomputable def parse : OracleBlock 8 := UnitRecognitionLabelRead.on parseEmbedding
noncomputable def convert (denominator : Bool) : OracleBlock 8 := UnarySignedRead.on (convertEmbedding denominator)
noncomputable def emit : OracleBlock 8 := rename wordEmit emitEmbedding
noncomputable def header : OracleBlock 8 := seq (convert true) emit
noncomputable def body : OracleBlock 8 := seq parse (seq (convert false) (seq (clear 4) emit))

def cellBound (B : ℕ) : ℕ := 4*B^2+22*B+40

lemma signed_length (n : ℕ) : (signedBits (n:ℤ)).length≤n+1 := by
  have h : (Computability.encodeNat n).length≤n := by
    rw [encodeNat_length];exact Nat.size_le.mpr Nat.lt_two_pow_self
  simpa [signedBits] using Nat.add_le_add_right h 1

lemma parse_executes (g : BitString → ℕ) (values : BitString) (D a : ℕ) (rest acc : BitString) :
    parse.Executes g (coreState values D [] (pairBits (List.replicate a true) rest) [] [] acc)
      (coreState values D [] rest (List.replicate a true) [] acc) (5*a+7) := by
  convert UnitRecognitionLabelRead.on_executes parseEmbedding g
    (coreState values D [] (pairBits (List.replicate a true) rest) [] [] acc)
    (coreState values D [] rest (List.replicate a true) [] acc) (List.replicate a true) rest
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
  simp

lemma convert_header_executes (g : BitString → ℕ) (values : BitString) (D : ℕ) (stream acc : BitString) :
    ∃t,(convert true).Executes g (coreState values D [] stream [] [] acc)
      (coreState values D [] stream [] (signedBits (D:ℤ)) acc) t ∧t≤UnarySignedRead.bound D := by
  obtain ⟨t,ht,hb⟩:=UnarySignedRead.on_executes (convertEmbedding true) g
    (coreState values D [] stream [] [] acc) D (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> rfl

lemma convert_value_executes (g : BitString → ℕ) (values : BitString) (D a : ℕ) (stream acc : BitString) :
    ∃t,(convert false).Executes g (coreState values D [] stream (List.replicate a true) [] acc)
      (coreState values D [] stream (List.replicate a true) (signedBits (a:ℤ)) acc) t ∧t≤UnarySignedRead.bound a := by
  obtain ⟨t,ht,hb⟩:=UnarySignedRead.on_executes (convertEmbedding false) g
    (coreState values D [] stream (List.replicate a true) [] acc) a (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> rfl

lemma emit_executes (g : BitString → ℕ) (values : BitString) (D : ℕ) (stream word acc : BitString) :
    emit.Executes g (coreState values D [] stream [] word acc)
      (coreState values D [] stream [] [] ((wordChunk word).reverse++acc)) (6*word.length+7) := by
  apply rename_executes_to wordEmit emitEmbedding g (wordEmit_executes g word acc)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim

lemma header_executes (g : BitString → ℕ) (values : BitString) (D : ℕ) (stream acc : BitString) :
    ∃t,header.Executes g (coreState values D [] stream [] [] acc)
      (coreState values D [] stream [] [] ((wordChunk (signedBits (D:ℤ))).reverse++acc)) t ∧t≤cellBound D := by
  obtain ⟨t,ht,hb⟩:=convert_header_executes g values D stream acc
  refine ⟨_,seq_executes _ _ g ht (emit_executes g values D stream (signedBits (D:ℤ)) acc),?_⟩
  have h:=signed_length D
  unfold cellBound UnarySignedRead.bound at *
  omega

lemma body_executes (g : BitString → ℕ) (values : BitString) (D a : ℕ) (rest acc : BitString) :
    ∃t,body.Executes g (coreState values D [] (pairBits (List.replicate a true) rest) [] [] acc)
      (coreState values D [] rest [] [] ((wordChunk (signedBits (a:ℤ))).reverse++acc)) t ∧t≤cellBound a := by
  have hp:=parse_executes g values D a rest acc
  obtain ⟨t,ht,hb⟩:=convert_value_executes g values D a rest acc
  have hc : (clear (4:Fin 9)).Executes g
      (coreState values D [] rest (List.replicate a true) (signedBits (a:ℤ)) acc)
      (coreState values D [] rest [] (signedBits (a:ℤ)) acc) (a+1) := by
    convert clear_executes g (4:Fin 9) (coreState values D [] rest (List.replicate a true) (signedBits (a:ℤ)) acc) using 1
    · funext i;fin_cases i <;> rfl
    · simp [coreState]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g ht (seq_executes _ _ g hc
    (emit_executes g values D rest (signedBits (a:ℤ)) acc))),?_⟩
  have h:=signed_length a
  unfold cellBound UnarySignedRead.bound at *
  omega

lemma cellBound_mono {a B : ℕ} (h : a≤B) : cellBound a≤cellBound B := by
  have hp:=Nat.pow_le_pow_left h 2
  unfold cellBound
  omega
lemma header_queryFree : header.QueryFree := seq_queryFree _ _ (UnarySignedRead.on_queryFree _)
  (rename_queryFree _ _ wordEmit_queryFree)
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (UnitRecognitionLabelRead.on_queryFree _)
  (seq_queryFree _ _ (UnarySignedRead.on_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (rename_queryFree _ _ wordEmit_queryFree)))
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
