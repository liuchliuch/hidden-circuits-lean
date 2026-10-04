import HiddenCircuits.Circuit.Runtime.SampleEmitterSetup

/-! A concrete finite compiler from canonical constraint
circuit bytes and unary sample indices to the canonical physical WordEval query. -/
namespace HiddenCircuits.Circuit.Runtime.SampleEmitter
open HiddenCircuits.Complexity OracleBlock

def rawBits {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) : BitString :=
  queryPrefix n++encodeBitList ((closedWord ((sampledConstraintCircuit w r s).map (DeltaGate.compileSample u))).map letterBits)

def outputStore (circuit : BitString) (r s u n : ℕ) (exponent sign query : BitString) : Store 31 := fun i =>
  if i.val=0 then circuit else if i.val=1 then List.replicate r true else if i.val=2 then List.replicate s true
  else if i.val=3 then List.replicate u true else if i.val=4 then List.replicate n true
  else if i.val=6 then exponent else if i.val=7 then sign else if i.val=31 then query else []
noncomputable def emit : OracleBlock 31 := seq setup (seq projection (seq gateLoop projection))
noncomputable def finish : OracleBlock 31 := seq (reverseOn 5 31 (by decide)) (clear 4)
noncomputable def program : OracleBlock 31 := seq emit finish
noncomputable def rawCost (n L m r s u : ℕ) : ℕ :=
  5*L+137*n+67+2*ProjectionStream.time.eval n+m*(gateTime n r s u+24*n+99)

lemma pairBits_unary (q : ℕ) (ys : BitString) :
    pairBits (List.replicate q true) ys=List.replicate (2*q) true++false::ys := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [List.replicate_succ,pairBits,ih,Nat.mul_succ]
    rfl

lemma rawBits_eq_wordBits {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (r s u : ℕ) :
    rawBits w r s u=wordBits (compileWordInstance hn
      ((sampledConstraintCircuit w r s).map (DeltaGate.compileSample u)) (zeroBits n) (zeroBits n)) := by
  unfold rawBits wordBits compileWordInstance
  simp only [BoundaryMask.stateBits_castTracks,BoundaryMask.zero_mask,List.map_map]
  have hletter {a b : ℕ} (h : a=b) (l : Letter a) : letterBits (Letter.castTracks h l)=letterBits l := by
    subst b;rfl
  simp only [Function.comp_def,hletter,pairBits_unary]
  change queryPrefix n++encodeBitList _=List.replicate (2*(2*n)) true++false::encodeBitList _
  rw [show 2*(2*n)=4*n by omega]
  simp only [queryPrefix,queryHeader,encodeBitList,BinaryArithmetic.pairBits_eq_payload,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]

set_option maxHeartbeats 800000 in
theorem emit_executes (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    ∃cost, emit.Executes g (store (circuitBits n w) r s u 0 0 0 [] [] [] [] [] [])
      (store (circuitBits n w) r s u n 0 0 [] [] [] (rawBits w r s u).reverse
        (List.replicate (SampleScalar.sampleExponent w r s u) true) [sampleNegative w false]) cost ∧
      cost ≤ rawCost n (circuitBits n w).length w.length r s u := by
  have h0 := setup_executes g w r s u
  let P := encodeBitList ((globalProjectionWord n).map letterBits)
  let E := SampleScalar.projectionExponent n
  obtain ⟨a,ha,hab⟩ := projection_executes g (circuitBits n w) r s u n 0 0
    (encodeBitList (w.map gateBits)) [] [] (queryPrefix n).reverse [] [false]
  obtain ⟨b,hb,hbb⟩ := gateLoop_executes g w (circuitBits n w) r s u
    (P.reverse++(queryPrefix n).reverse) (List.replicate E true++[]) false
  obtain ⟨c,hc,hcb⟩ := projection_executes g (circuitBits n w) r s u n 0 0 [] [] []
    ((sampleOutput w r s u).reverse++(P.reverse++(queryPrefix n).reverse))
    (List.replicate (sampleGain w r s u) true++(List.replicate E true++[])) [sampleNegative w false]
  have he : E+(sampleGain w r s u+E)=SampleScalar.sampleExponent w r s u := by
    have h:=sampleGain_eq w r s u
    dsimp only [E]
    omega
  refine ⟨5*(circuitBits n w).length+137*n+60+(a+(b+c+2)+2)+2,?_,?_⟩
  · have h := seq_executes _ _ g h0 (seq_executes _ _ g ha (seq_executes _ _ g hb hc))
    convert h using 1
    · simp only [rawBits,closedWord,List.map_append,BinaryArithmetic.encodeBitList_append,
        List.reverse_append,sampleOutput,P,List.append_assoc]
      congr 1
      simp only [←List.append_assoc,←List.replicate_add,List.append_nil]
      congr 1
      dsimp only [E] at he
      omega
  · unfold rawCost
    omega

set_option maxHeartbeats 800000 in
theorem finish_executes (g : BitString → ℕ) (circuit : BitString) (r s u n : ℕ)
    (query exponent sign : BitString) :
    finish.Executes g (store circuit r s u n 0 0 [] [] [] query.reverse exponent sign)
      (outputStore circuit r s u 0 exponent sign query) (2*query.length+n+4) := by
  have hr : (reverseOn (5:Fin 32) 31 (by decide)).Executes g
      (store circuit r s u n 0 0 [] [] [] query.reverse exponent sign)
      (outputStore circuit r s u n exponent sign query) (2*query.length+1) := by
    convert reverseOn_executes g (5:Fin 32) 31 (by decide)
      (store circuit r s u n 0 0 [] [] [] query.reverse exponent sign) using 1
    · funext i;fin_cases i <;> simp [store,outputStore]
    · simp [store]
  have hc : (clear (4:Fin 32)).Executes g (outputStore circuit r s u n exponent sign query)
      (outputStore circuit r s u 0 exponent sign query) (n+1) := by
    convert clear_executes g (4:Fin 32) (outputStore circuit r s u n exponent sign query) using 1
    · funext i;fin_cases i <;> rfl
    · simp [outputStore]
  convert seq_executes _ _ g hr hc using 1 <;> omega

theorem program_executes_raw (g : BitString → ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    ∃cost, program.Executes g (store (circuitBits n w) r s u 0 0 0 [] [] [] [] [] [])
      (outputStore (circuitBits n w) r s u 0
        (List.replicate (SampleScalar.sampleExponent w r s u) true) [sampleNegative w false] (rawBits w r s u)) cost ∧
      cost ≤ rawCost n (circuitBits n w).length w.length r s u+2*(rawBits w r s u).length+n+6 := by
  obtain ⟨a,ha,hab⟩ := emit_executes g w r s u
  have hb := finish_executes g (circuitBits n w) r s u n (rawBits w r s u)
    (List.replicate (SampleScalar.sampleExponent w r s u) true) [sampleNegative w false]
  exact ⟨_,seq_executes _ _ g ha hb,by omega⟩

lemma emit_queryFree : emit.QueryFree := seq_queryFree _ _ setup_queryFree
  (seq_queryFree _ _ projection_queryFree (seq_queryFree _ _ gateLoop_queryFree projection_queryFree))
lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (reverseOn_queryFree _ _ _) (clear_queryFree _)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ emit_queryFree finish_queryFree
end HiddenCircuits.Circuit.Runtime.SampleEmitter
