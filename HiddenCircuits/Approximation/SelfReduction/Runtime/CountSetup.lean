import HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetupFrame

/-! A total query-free raw-input setup program for the endpoint FPRAS. Its clock
is polynomial in all raw input bits, while its sampling budget depends only on
the pre-random request length. Port69 is the sole gate to the counting loop. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime Polynomial
set_option maxHeartbeats 1500000

lemma finishBlock_executes (g : BitString → ℕ) (raw : BitString) :
    finishBlock.Executes g (guarded raw) (output raw) (3*size raw+18) := by
  let bits : Fin 73 → Bool := fun i => if i.val=36 then (parse raw).ok
    else if i.val=38 then (parse (request raw)).ok
    else if i.val=70 then SamplerRuntime.EndpointParser.valid (graph raw) else tapeLong raw
  let decided := Function.update (eraseStore [36,38,70,41] (hCleared raw)) (69:Fin 73) [ready raw]
  have hc : (clear (42:Fin 73)).Executes g (guarded raw) (hCleared raw) (3*size raw+1) := by
    simpa [hCleared,guarded,generated,parameterPolynomial] using clear_executes g (42:Fin 73) (guarded raw)
  have hd : (decision (69:Fin 73) [36,38,70,41] allFour).Executes g (hCleared raw) decided 12 := by
    have hh := decision_executes (69:Fin 73) [36,38,70,41] (by decide) (by decide) allFour bits g (hCleared raw)
      (by intro i hi;fin_cases i <;> simp_all [hCleared,guarded,generated,depthCopied,validatedClean,parsed,bits])
    simpa [decided,ready,bits,allFour,hCleared,guarded,generated,depthCopied,validatedClean,parsed] using hh
  have hp : (push (70:Fin 73) true).Executes g decided (output raw) 1 := by
    convert push_executes g (70:Fin 73) true decided using 1
    funext i;fin_cases i <;> simp [decided,output,eraseStore]
  convert seq_executes _ _ g hc (seq_executes _ _ g hd hp) using 1 <;> omega

lemma lengths (raw : BitString) : size raw≤raw.length ∧ (coins raw).length≤raw.length ∧
    (graph raw).length≤size raw ∧ (dimension raw).length≤(graph raw).length := by
  have h := parse_lengths raw
  have hg := parse_lengths (request raw)
  have hd := SamplerRuntime.EndpointParser.fields_lengths (graph raw)
  exact ⟨h.1,h.2,hg.1,hd.1⟩

noncomputable def time : Polynomial ℕ :=
  (40*X+100)+(SamplerRuntime.EndpointParser.time+2*X+6)+(5*X+2)+parametersTime+
    30*(X+SelfReduction.EndpointResidual.randomBitsPolynomial+1)+(3*X+18)+10

/-- Every binary input, including malformed requests and truncated tapes, reaches
this exact prepared store in fixed polynomial time. No certificate is supplied. -/
theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃c,program.Executes g (input raw) (output raw) c ∧ c≤time.eval raw.length := by
  obtain ⟨a,ha,hab⟩ := parseBlock_executes g raw
  obtain ⟨b,hb,hbb⟩ := validateBlock_executes g raw
  have hd := depthBlock_executes g raw
  have hp := parametersBlock_executes g raw
  obtain ⟨c,hc,hcb⟩ := guardBlock_executes g raw
  have hf := finishBlock_executes g raw
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hd
    (seq_executes _ _ g hp (seq_executes _ _ g hc hf)))),?_⟩
  have hl := lengths raw
  have hgraph := hl.2.2.1.trans hl.1
  have hdim := hl.2.2.2.trans hgraph
  have hpt := polynomial_nat_eval_mono parametersTime hl.1
  have het := polynomial_nat_eval_mono SamplerRuntime.EndpointParser.time hgraph
  have hrt := polynomial_nat_eval_mono SelfReduction.EndpointResidual.randomBitsPolynomial hl.1
  dsimp only at hpt het hrt
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ front_queryFree)
  (seq_queryFree _ _ (seq_queryFree _ _ (rename_queryFree _ _ SamplerRuntime.EndpointParser.program_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ parameters_queryFree)
      (seq_queryFree _ _ (rename_queryFree _ _ tapeGuard_queryFree)
        (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (decision_queryFree _ _ _) (push_queryFree _ _)))))))

/-- Explicit bit-storage bound follows from actual charged instruction steps. -/
theorem program_storage (g : BitString → ℕ) (raw : BitString) (i : Fin 73) :
    (output raw i).length≤raw.length+time.eval raw.length := by
  obtain ⟨c,hc,hb⟩ := program_executes g raw
  have hs : ∀j,(input raw j).length≤raw.length := by
    intro j;simp only [input];split_ifs <;> simp
  exact (hc.stack_bound hs i).trans (Nat.add_le_add_left hb _)

lemma ready_iff (raw : BitString) : ready raw=true ↔
    (parse raw).ok=true ∧ (parse (request raw)).ok=true ∧
      (GraphReduction.MonotoneEndpointEncoding.decode (graph raw)).isSome=true ∧
      SelfReduction.EndpointResidual.randomBitsPolynomial.eval (size raw)≤(coins raw).length := by
  simp [ready,SamplerRuntime.EndpointParser.valid_eq_decode,tapeLong,and_assoc]

theorem canonical_ready (E : GraphReduction.MonotoneEndpointEncoding.Input) (r k : ℕ) (tape : BitString)
    (ht : SelfReduction.EndpointResidual.randomBitsPolynomial.eval
      (estimateInput (GraphReduction.MonotoneEndpointEncoding.encode E) r k).length≤tape.length) :
    ready (pairBits (estimateInput (GraphReduction.MonotoneEndpointEncoding.encode E) r k) tape)=true := by
  simpa [ready,request,estimateInput,graph,coins,size,tapeLong,SamplerRuntime.EndpointParser.valid_encode] using ht

/-- On every accepted raw input the graph is genuinely canonical and the stored
header is unary. Arbitrary precision payloads are deliberately ignored. -/
theorem accepted_input (raw : BitString) (hr : ready raw=true) :
    ∃E : GraphReduction.MonotoneEndpointEncoding.Input,
      GraphReduction.MonotoneEndpointEncoding.encode E=graph raw ∧
      dimension raw=List.replicate E.1 true ∧ E.1≤size raw ∧
      SelfReduction.EndpointResidual.randomBitsPolynomial.eval (size raw)≤(coins raw).length := by
  have hs := (ready_iff raw).mp hr
  obtain ⟨E,hE⟩ := Option.isSome_iff_exists.mp hs.2.2.1
  refine ⟨E,GraphReduction.MonotoneEndpointEncoding.decode_some hE,
    (SamplerRuntime.EndpointParser.fields_of_decode hE).1,?_,hs.2.2.2⟩
  exact (GraphReduction.MonotoneEndpointEncoding.size_le_of_decode hE).trans (lengths raw).2.2.1

lemma canonical_bounds (E : GraphReduction.MonotoneEndpointEncoding.Input) (r k : ℕ) :
    E.1≤(estimateInput (GraphReduction.MonotoneEndpointEncoding.encode E) r k).length ∧
    r≤(estimateInput (GraphReduction.MonotoneEndpointEncoding.encode E) r k).length ∧
    k≤(estimateInput (GraphReduction.MonotoneEndpointEncoding.encode E) r k).length := by
  have hd := GraphReduction.MonotoneEndpointEncoding.size_le_of_decode
    (GraphReduction.MonotoneEndpointEncoding.decode_encode E)
  simp only [estimateInput_length]
  omega
end HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
