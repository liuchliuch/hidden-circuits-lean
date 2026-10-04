import HiddenCircuits.Circuit.Runtime.SourceSampleFrame
import HiddenCircuits.Circuit.Runtime.CircuitMetadata
import HiddenCircuits.Complexity.DeltaEncoding

/-! Byte-only initialization for the independent Delta-to-Word reduction.
The degree is counted from physically parsed gate tags, not supplied as a certificate. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaWordSetup
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

def initial (bits : BitString) : Store 63 := Function.update (fun _ => []) 0 bits

def parametersFor (bits : BitString) : SourceSample.Parameters where
  circuit := bits
  normalization := 0
  firstCount := 0
  secondCount := 0
  r := 0
  s := 0
  u := 0
  firstNumerators := []
  secondNumerators := []
  firstDenominator := signedBits 1
  secondDenominator := signedBits 1

def parameters {n : ℕ} (w : List (DeltaGate n)) : SourceSample.Parameters :=
  parametersFor (Runtime.circuitBits n (w.map DeltaGate.descriptor))

def workStore (bits : BitString) (n f d : ℕ) : Store 63 := fun i =>
  if i.val=0 then bits else if i.val=23 then List.replicate n true
  else if i.val=5 then List.replicate f true else if i.val=13 then List.replicate d true else []

def metadataEmbedding : Fin 9 ↪ Fin 64 where
  toFun i := (![0,23,5,6,24,25,26,27,28] : Fin 9 → Fin 64) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def metadata : OracleBlock 63 := CircuitMetadata.on metadataEmbedding
noncomputable def double : OracleBlock 63 := repeatPrepend 5 13 [true,true]
noncomputable def constants : OracleBlock 63 :=
  seq (prepend 9 (signedBits 1)) (seq (prepend 10 (signedBits 1))
    (seq (push 11 false) (seq (prepend 12 (signedBits 1))
      (seq (push 55 false) (seq (push 56 false) (push 57 false))))))
noncomputable def program : OracleBlock 63 := seq metadata (seq double (seq (clear 23) constants))
noncomputable def time : Polynomial ℕ := CircuitMetadata.time+10*X+45

lemma descriptor_first {n : ℕ} (a : DeltaGate n) :
    CircuitMetadata.first (Runtime.gateTag (DeltaGate.descriptor a))=DeltaGate.mark a := by
  cases a with
  | one p a => cases a <;> rfl
  | constraint p => rfl
lemma descriptor_second {n : ℕ} (a : DeltaGate n) :
    CircuitMetadata.second (Runtime.gateTag (DeltaGate.descriptor a))=0 := by
  cases a with
  | one p a => cases a <;> rfl
  | constraint p => rfl
lemma descriptor_forbid {n : ℕ} (w : List (DeltaGate n)) :
    forbidOccurrences (w.map DeltaGate.descriptor)=deltaOccurrences w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons,CircuitMetadata.forbid_cons,descriptor_first,ih,
      deltaOccurrences,List.map_cons,List.sum_cons]
lemma descriptor_sign {n : ℕ} (w : List (DeltaGate n)) :
    signOccurrences (w.map DeltaGate.descriptor)=0 := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons,CircuitMetadata.sign_cons,descriptor_second,ih,Nat.zero_add]

set_option maxHeartbeats 600000 in
lemma metadata_executes (g : BitString → ℕ) {n : ℕ} (w : List (DeltaGate n)) :
    ∃c,metadata.Executes g (initial (Runtime.circuitBits n (w.map DeltaGate.descriptor)))
      (workStore (Runtime.circuitBits n (w.map DeltaGate.descriptor)) n (deltaOccurrences w) 0) c ∧
      c≤CircuitMetadata.time.eval (Runtime.circuitBits n (w.map DeltaGate.descriptor)).length := by
  obtain ⟨c,hc,hb⟩ := CircuitMetadata.on_executes metadataEmbedding g
    (initial (Runtime.circuitBits n (w.map DeltaGate.descriptor))) (w.map DeltaGate.descriptor)
    (by funext i;fin_cases i <;> rfl)
  refine ⟨c,?_,hb⟩
  simp only [show metadataEmbedding 1=23 from rfl,show metadataEmbedding 2=5 from rfl,
    show metadataEmbedding 3=6 from rfl,descriptor_forbid,descriptor_sign] at hc
  convert hc using 1
  funext i;fin_cases i <;> simp [initial,workStore]

lemma flatten_double (f : ℕ) : (List.replicate f [true,true]).flatten=List.replicate (2*f) true := by
  induction f with
  | zero => rfl
  | succ f ih =>
    simp only [List.replicate_succ,List.flatten_cons,ih]
    rw [Nat.mul_succ,Nat.add_comm (2*f),List.replicate_add]
    rfl

set_option maxHeartbeats 600000 in
lemma double_executes (g : BitString → ℕ) (bits : BitString) (n f : ℕ) :
    double.Executes g (workStore bits n f 0) (workStore bits n 0 (2*f)) (9*f+1) := by
  convert repeatPrepend_executes g (5:Fin 64) 13 (by decide) [true,true] (workStore bits n f 0) using 1
  · funext i;fin_cases i <;> simp [workStore,flatten_double]
  · simp [workStore]

set_option maxHeartbeats 600000 in
lemma clear_executes (g : BitString → ℕ) (bits : BitString) (n d : ℕ) :
    (clear (23:Fin 64)).Executes g (workStore bits n 0 d) (workStore bits 0 0 d) (n+1) := by
  convert OracleBlock.clear_executes g (23:Fin 64) (workStore bits n 0 d) using 1
  · funext i;fin_cases i <;> simp [workStore]
  · simp [workStore]

set_option maxHeartbeats 600000 in
lemma constants_executes (g : BitString → ℕ) (bits : BitString) (d : ℕ) :
    constants.Executes g (workStore bits 0 0 d)
      (SourceSample.store (parametersFor bits) {accumulator:=(0,1),degree:=d}) 37 := by
  let s0:=workStore bits 0 0 d
  let s1:=Function.update s0 (9:Fin 64) (signedBits 1)
  let s2:=Function.update s1 (10:Fin 64) (signedBits 1)
  let s3:=Function.update s2 (11:Fin 64) [false]
  let s4:=Function.update s3 (12:Fin 64) (signedBits 1)
  let s5:=Function.update s4 (55:Fin 64) [false]
  let s6:=Function.update s5 (56:Fin 64) [false]
  have h1 : (prepend (9:Fin 64) (signedBits 1)).Executes g s0 s1 7 := by
    simpa only [s1,show s0 9=[] from rfl,List.append_nil] using prepend_executes g (9:Fin 64) (signedBits 1) s0
  have h2 : (prepend (10:Fin 64) (signedBits 1)).Executes g s1 s2 7 := by
    simpa only [s2,show s1 10=[] from rfl,List.append_nil] using prepend_executes g (10:Fin 64) (signedBits 1) s1
  have h3 : (push (11:Fin 64) false).Executes g s2 s3 1 := by
    simpa only [s3,show s2 11=[] from rfl] using push_executes g (11:Fin 64) false s2
  have h4 : (prepend (12:Fin 64) (signedBits 1)).Executes g s3 s4 7 := by
    simpa only [s4,show s3 12=[] from rfl,List.append_nil] using prepend_executes g (12:Fin 64) (signedBits 1) s3
  have h5 : (push (55:Fin 64) false).Executes g s4 s5 1 := by
    simpa only [s5,show s4 55=[] from rfl] using push_executes g (55:Fin 64) false s4
  have h6 : (push (56:Fin 64) false).Executes g s5 s6 1 := by
    simpa only [s6,show s5 56=[] from rfl] using push_executes g (56:Fin 64) false s5
  have h7 : (push (57:Fin 64) false).Executes g s6
      (SourceSample.store (parametersFor bits) {accumulator:=(0,1),degree:=d}) 1 := by
    convert push_executes g (57:Fin 64) false s6 using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6 h7)))))

theorem program_executes (g : BitString → ℕ) {n : ℕ} (w : List (DeltaGate n)) :
    ∃c,program.Executes g (initial (Runtime.circuitBits n (w.map DeltaGate.descriptor)))
      (SourceSample.store (parameters w) {accumulator:=(0,1),degree:=2*deltaOccurrences w}) c ∧
      c≤time.eval (Runtime.circuitBits n (w.map DeltaGate.descriptor)).length := by
  obtain ⟨c,hc,hb⟩ := metadata_executes g w
  have hd:=double_executes g (Runtime.circuitBits n (w.map DeltaGate.descriptor)) n (deltaOccurrences w)
  have hn:=clear_executes g (Runtime.circuitBits n (w.map DeltaGate.descriptor)) n (2*deltaOccurrences w)
  have hk:=constants_executes g (Runtime.circuitBits n (w.map DeltaGate.descriptor)) (2*deltaOccurrences w)
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hd (seq_executes _ _ g hn hk)),?_⟩
  have hnB : n≤(Runtime.circuitBits n (w.map DeltaGate.descriptor)).length := by
    simp only [Runtime.circuitBits,pairBits_length,List.length_replicate];omega
  have hfB : deltaOccurrences w≤(Runtime.circuitBits n (w.map DeltaGate.descriptor)).length := by
    have hf:=deltaOccurrences_le_length w
    have hw:=list_length_le_encodeBitList_length ((w.map DeltaGate.descriptor).map Runtime.gateBits)
    simp only [List.length_map] at hw
    simp only [Runtime.circuitBits,pairBits_length,List.length_replicate]
    omega
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

lemma metadata_queryFree : metadata.QueryFree := CircuitMetadata.on_queryFree _
lemma double_queryFree : double.QueryFree := repeatPrepend_queryFree _ _ _
lemma constants_queryFree : constants.QueryFree :=
  seq_queryFree _ _ (prepend_queryFree _ _) (seq_queryFree _ _ (prepend_queryFree _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (prepend_queryFree _ _)
      (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))))
lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ metadata_queryFree (seq_queryFree _ _ double_queryFree
    (seq_queryFree _ _ (clear_queryFree _) constants_queryFree))

end HiddenCircuits.Circuit.Runtime.DeltaWordSetup
