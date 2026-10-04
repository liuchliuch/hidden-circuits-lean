import HiddenCircuits.Circuit.Runtime.SamplePairParser
import HiddenCircuits.Circuit.Runtime.SampleGateDispatch
import HiddenCircuits.Complexity.OracleMove

/-! Actual canonical circuit parsing and unary occurrence
counts, with a fixed finite register bank and complete work cleanup. -/
namespace HiddenCircuits.Circuit.Runtime.CircuitMetadata
open HiddenCircuits.Complexity OracleBlock Polynomial

def store (circuit : BitString) (n f z : ℕ) (stream atom tag : BitString) : Store 8 := fun i =>
  if i.val=0 then circuit else if i.val=1 then List.replicate n true else
  if i.val=2 then List.replicate f true else if i.val=3 then List.replicate z true else
  if i.val=4 then stream else if i.val=5 then atom else if i.val=6 then tag else []
def first (t : GateTag) : ℕ := if t=.forbid then 1 else 0
def second (t : GateTag) : ℕ := if t=.controlledSign then 1 else 0
noncomputable def countTag (t : GateTag) : OracleBlock 8 :=
  match t with | .forbid => push 2 true | .controlledSign => push 3 true | _ => skip
noncomputable def dispatch : OracleBlock 8 := SampleGateDispatch.block 6 countTag

def circuitEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := (![4,1,7,8] : Fin 4 → Fin 9) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def gateEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := (![4,5,7,8] : Fin 4 → Fin 9) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def atomEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := (![5,6,7,8] : Fin 4 → Fin 9) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def body : OracleBlock 8 := seq (SamplePairParser.on gateEmbedding)
  (seq (SamplePairParser.on atomEmbedding) (seq (clear 5) dispatch))
noncomputable def loop : OracleBlock 8 := whilePop 4 body body
noncomputable def setup : OracleBlock 8 := seq (copyOn 0 4 8 (by decide) (by decide) (by decide))
  (SamplePairParser.on circuitEmbedding)
noncomputable def program : OracleBlock 8 := seq setup loop
noncomputable def time : Polynomial ℕ := 6*X^2+110*X+20

lemma forbid_cons {n : ℕ} (a : ConstraintGate n) (w : List (ConstraintGate n)) :
    forbidOccurrences (a::w)=first (gateTag a)+forbidOccurrences w := by
  cases a with
  | one p g => cases g <;> simp [forbidOccurrences,first,gateTag,ConstraintGate.spectral,firstMarks,Nat.add_comm]
  | forbid p => simp [forbidOccurrences,first,gateTag,ConstraintGate.spectral,firstMarks,Nat.add_comm]
  | controlledSign p => simp [forbidOccurrences,first,gateTag,ConstraintGate.spectral,firstMarks,Nat.add_comm]
lemma sign_cons {n : ℕ} (a : ConstraintGate n) (w : List (ConstraintGate n)) :
    signOccurrences (a::w)=second (gateTag a)+signOccurrences w := by
  cases a with
  | one p g => cases g <;> simp [signOccurrences,second,gateTag,ConstraintGate.spectral,secondMarks,Nat.add_comm]
  | forbid p => simp [signOccurrences,second,gateTag,ConstraintGate.spectral,secondMarks,Nat.add_comm]
  | controlledSign p => simp [signOccurrences,second,gateTag,ConstraintGate.spectral,secondMarks,Nat.add_comm]

set_option maxHeartbeats 600000 in
lemma dispatch_executes (g : BitString → ℕ) (t : GateTag) (circuit : BitString) (n f z : ℕ) (stream : BitString) :
    dispatch.Executes g (store circuit n f z stream [] t.bits)
      (store circuit n (f+first t) (z+second t) stream [] []) 9 := by
  apply SampleGateDispatch.block_executes 6 countTag g t _ _ 1 rfl
  cases t <;> first
  | (convert push_executes g (2:Fin 9) true (Function.update (store circuit n f z stream [] GateTag.forbid.bits) 6 []) using 1
     funext i;fin_cases i <;> simp [store,first,second,List.replicate_succ])
  | (convert push_executes g (3:Fin 9) true (Function.update (store circuit n f z stream [] GateTag.controlledSign.bits) 6 []) using 1
     funext i;fin_cases i <;> simp [store,first,second,List.replicate_succ])
  | (convert skip_executes g (Function.update (store circuit n f z stream [] _) 6 []) using 1
     funext i;fin_cases i <;> simp [store,first,second])

set_option maxHeartbeats 600000 in
lemma body_executes (g : BitString → ℕ) {n : ℕ} (a : ConstraintGate n) (circuit : BitString)
    (f z : ℕ) (stream : BitString) :
    body.Executes g (store circuit n f z (pairBits (gateBits a) stream) [] [])
      (store circuit n (f+first (gateTag a)) (z+second (gateTag a)) stream [] []) (6*gatePosition a+95) := by
  have h1 : (SamplePairParser.on gateEmbedding).Executes g
      (store circuit n f z (pairBits (gateBits a) stream) [] [])
      (store circuit n f z stream (gateBits a) []) (5*(gatePosition a+9)+7) := by
    convert SamplePairParser.on_executes gateEmbedding g (gateBits a) stream
      (store circuit n f z (pairBits (gateBits a) stream) [] []) (store circuit n f z stream (gateBits a) [])
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    rw [gateBits_length]
  have h2 : (SamplePairParser.on atomEmbedding).Executes g
      (store circuit n f z stream (gateBits a) [])
      (store circuit n f z stream (List.replicate (gatePosition a) true) (gateTag a).bits) 27 := by
    convert SamplePairParser.on_executes atomEmbedding g (gateTag a).bits (List.replicate (gatePosition a) true)
      (store circuit n f z stream (gateBits a) [])
      (store circuit n f z stream (List.replicate (gatePosition a) true) (gateTag a).bits)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  have h3 : (clear (5:Fin 9)).Executes g
      (store circuit n f z stream (List.replicate (gatePosition a) true) (gateTag a).bits)
      (store circuit n f z stream [] (gateTag a).bits) (gatePosition a+1) := by
    convert clear_executes g (5:Fin 9) (store circuit n f z stream (List.replicate (gatePosition a) true) (gateTag a).bits) using 1
    · funext i;fin_cases i <;> rfl
    · simp [store]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (dispatch_executes g (gateTag a) circuit n f z stream))) using 1 <;> omega

set_option maxHeartbeats 600000 in
lemma loop_execution (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (circuit : BitString) (f z : ℕ) :
    ∃c, WhileExecution (4:Fin 9) body body g (store circuit n f z (encodeBitList (w.map gateBits)) [] [])
      (store circuit n (f+forbidOccurrences w) (z+signOccurrences w) [] [] []) c ∧ c≤w.length*(6*n+97)+1 := by
  induction w generalizing f z with
  | nil => exact ⟨1,by simpa [forbidOccurrences,signOccurrences,firstMarks,secondMarks] using
      (WhileExecution.empty (stack:=(4:Fin 9)) (B:=body) (C:=body) (g:=g) (store circuit n f z [] [] []) rfl),by simp⟩
  | cons a w ih =>
    have hb := body_executes g a circuit f z (encodeBitList (w.map gateBits))
    have hu : Function.update (store circuit n f z (encodeBitList ((a::w).map gateBits)) [] []) (4:Fin 9)
        (pairBits (gateBits a) (encodeBitList (w.map gateBits)))=
        store circuit n f z (pairBits (gateBits a) (encodeBitList (w.map gateBits))) [] [] := by
      funext i;fin_cases i <;> rfl
    rw [←hu] at hb
    obtain ⟨c,hc,hcb⟩ := ih (f+first (gateTag a)) (z+second (gateTag a))
    have h := WhileExecution.one (stack:=(4:Fin 9)) (B:=body) (C:=body) (g:=g) rfl hb hc
    refine ⟨1+(6*gatePosition a+95)+1+c,?_,?_⟩
    · simpa only [forbid_cons,sign_cons,Nat.add_assoc] using h
    · have hp : gatePosition a≤n := by have h:=gatePosition_bound a;omega
      simp only [List.length_cons]
      nlinarith

lemma setup_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) :
    setup.Executes g (store (circuitBits n w) 0 0 0 [] [] [])
      (store (circuitBits n w) n 0 0 (encodeBitList (w.map gateBits)) [] []) (5*(circuitBits n w).length+5*n+11) := by
  have hc : (copyOn (0:Fin 9) 4 8 (by decide) (by decide) (by decide)).Executes g
      (store (circuitBits n w) 0 0 0 [] [] []) (store (circuitBits n w) 0 0 0 (circuitBits n w) [] []) (5*(circuitBits n w).length+2) := by
    convert copyOn_executes g (0:Fin 9) 4 8 (by decide) (by decide) (by decide) (store (circuitBits n w) 0 0 0 [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [store]
  have hp : (SamplePairParser.on circuitEmbedding).Executes g (store (circuitBits n w) 0 0 0 (circuitBits n w) [] [])
      (store (circuitBits n w) n 0 0 (encodeBitList (w.map gateBits)) [] []) (5*n+7) := by
    convert SamplePairParser.on_executes circuitEmbedding g (List.replicate n true) (encodeBitList (w.map gateBits))
      (store (circuitBits n w) 0 0 0 (circuitBits n w) [] []) (store (circuitBits n w) n 0 0 (encodeBitList (w.map gateBits)) [] [])
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  convert seq_executes _ _ g hc hp using 1 <;> omega

theorem program_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) :
    ∃c, program.Executes g (store (circuitBits n w) 0 0 0 [] [] [])
      (store (circuitBits n w) n (forbidOccurrences w) (signOccurrences w) [] [] []) c ∧
      c≤time.eval (circuitBits n w).length := by
  obtain ⟨c,hc,hb⟩ := loop_execution g w (circuitBits n w) 0 0
  simp only [Nat.zero_add] at hc
  refine ⟨_,seq_executes _ _ g (setup_executes g w) (whilePop_executes _ _ _ g hc),?_⟩
  have hn : n≤(circuitBits n w).length := by simp only [circuitBits,pairBits_length,List.length_replicate];omega
  have hw : w.length≤(circuitBits n w).length := by
    have h:=list_length_le_encodeBitList_length (w.map gateBits)
    simp only [List.length_map] at h
    simp only [circuitBits,pairBits_length,List.length_replicate]
    omega
  have hm := Nat.mul_le_mul hw (show 6*n+97≤6*(circuitBits n w).length+97 by omega)
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
  nlinarith

lemma countTag_queryFree (t : GateTag) : (countTag t).QueryFree := by cases t <;> first | exact push_queryFree _ _ | exact skip_queryFree
lemma dispatch_queryFree : dispatch.QueryFree := SampleGateDispatch.block_queryFree _ _ countTag_queryFree
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (SamplePairParser.on_queryFree _)
  (seq_queryFree _ _ (SamplePairParser.on_queryFree _) (seq_queryFree _ _ (clear_queryFree _) dispatch_queryFree))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (SamplePairParser.on_queryFree _))
  (whilePop_queryFree _ _ _ body_queryFree body_queryFree)

noncomputable def on {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    {n : ℕ} (w : List (ConstraintGate n))
    (hs : s∘φ=store (circuitBits n w) 0 0 0 [] [] []) :
    ∃c, (on φ).Executes g s (Function.update (Function.update (Function.update s (φ 1)
      (List.replicate n true)) (φ 2) (List.replicate (forbidOccurrences w) true)) (φ 3) (List.replicate (signOccurrences w) true)) c ∧
      c≤time.eval (circuitBits n w).length := by
  obtain ⟨c,hc,hb⟩ := program_executes g w
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g hc hs
  · funext i
    have hi:=congrFun hs i
    change s (φ i)=_ at hi
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hi]
    fin_cases i <;> rfl
  · intro i hi;simp only [Function.update_of_ne (hi 1).symm,Function.update_of_ne (hi 2).symm,Function.update_of_ne (hi 3).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 9 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.CircuitMetadata
