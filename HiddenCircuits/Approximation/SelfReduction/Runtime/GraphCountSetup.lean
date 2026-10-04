import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetupFrame

/-! Total query-free raw-input setup for dense graph counting. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime Polynomial
set_option maxHeartbeats 1500000

lemma finishBlock_executes (g : BitString → ℕ) (raw : BitString) :
    finishBlock.Executes g (guarded raw) (output raw) (3*size raw+20) := by
  let bits : Fin 73 → Bool := fun i => if i.val=36 then (parse raw).ok
    else if i.val=38 then (parse (request raw)).ok
    else if i.val=70 then (GraphInput.decode (graph raw)).isSome
    else if i.val=68 then even raw else tapeLong raw
  let decided := Function.update (eraseStore [36,38,70,41,68] (hCleared raw)) (69:Fin 73) [ready raw]
  have hc : (clear (42:Fin 73)).Executes g (guarded raw) (hCleared raw) (3*size raw+1) := by
    simpa [hCleared,guarded,generated,parameterPolynomial] using clear_executes g (42:Fin 73) (guarded raw)
  have hd : (decision (69:Fin 73) [36,38,70,41,68] allFive).Executes g (hCleared raw) decided 14 := by
    have hh := decision_executes (69:Fin 73) [36,38,70,41,68] (by decide) (by decide) allFive bits g (hCleared raw)
      (by intro i hi;fin_cases i <;> simp_all [hCleared,guarded,generated,depthCopied,halved,validatedClean,parsed,bits])
    simpa [decided,ready,bits,allFive,hCleared,guarded,generated,depthCopied,halved,validatedClean,parsed] using hh
  have hp : (push (70:Fin 73) true).Executes g decided (output raw) 1 := by
    convert push_executes g (70:Fin 73) true decided using 1
    funext i;fin_cases i <;> simp [decided,output,eraseStore]
  convert seq_executes _ _ g hc (seq_executes _ _ g hd hp) using 1 <;> omega

lemma lengths (raw : BitString) : size raw≤raw.length ∧ (coins raw).length≤raw.length ∧
    (graph raw).length≤size raw ∧ (dimension raw).length≤(graph raw).length := by
  have h := parse_lengths raw
  have hg := parse_lengths (request raw)
  have hd := parse_lengths (graph raw)
  exact ⟨h.1,h.2,hg.1,hd.1⟩

noncomputable def time : Polynomial ℕ :=
  (40*X+100)+(SamplerRuntime.GraphParser.time+X+3)+(7*X+6)+parametersTime+
    30*(X+SelfReduction.GraphCount.randomBitsPolynomial+1)+(3*X+20)+10

/-- Every binary input reaches the exact prepared store in polynomial time. -/
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
  have hdepth : depth raw≤raw.length := (Nat.div_le_self _ _).trans hdim
  have hpt := polynomial_nat_eval_mono parametersTime hl.1
  have het := polynomial_nat_eval_mono SamplerRuntime.GraphParser.time hgraph
  have hrt := polynomial_nat_eval_mono SelfReduction.GraphCount.randomBitsPolynomial hl.1
  dsimp only at hpt het hrt
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ front_queryFree)
  (seq_queryFree _ _ (seq_queryFree _ _ (rename_queryFree _ _ SamplerRuntime.GraphParser.program_queryFree)
    (clear_queryFree _))
    (seq_queryFree _ _ (seq_queryFree _ _ (rename_queryFree _ _ Halve.program_queryFree)
      (copyOn_queryFree _ _ _ _ _ _)) (seq_queryFree _ _ (rename_queryFree _ _ parameters_queryFree)
      (seq_queryFree _ _ (rename_queryFree _ _ tapeGuard_queryFree)
        (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (decision_queryFree _ _ _) (push_queryFree _ _)))))))

theorem program_storage (g : BitString → ℕ) (raw : BitString) (i : Fin 73) :
    (output raw i).length≤raw.length+time.eval raw.length := by
  obtain ⟨c,hc,hb⟩ := program_executes g raw
  have hs : ∀j,(input raw j).length≤raw.length := by
    intro j;simp only [input];split_ifs <;> simp
  exact (hc.stack_bound hs i).trans (Nat.add_le_add_left hb _)

lemma ready_iff (raw : BitString) : ready raw=true ↔
    (parse raw).ok=true ∧ (parse (request raw)).ok=true ∧
      (GraphInput.decode (graph raw)).isSome=true ∧
      SelfReduction.GraphCount.randomBitsPolynomial.eval (size raw)≤(coins raw).length ∧
      (dimension raw).length%2=0 := by
  simp [ready,tapeLong,even,and_assoc]

lemma dimension_of_decode {raw : BitString} {G : GraphInput} (h : GraphInput.decode (graph raw)=some G) :
    dimension raw=List.replicate G.1 true := (SamplerRuntime.GraphParser.output_fields h).1

lemma depth_of_decode {raw : BitString} {G : GraphInput} (h : GraphInput.decode (graph raw)=some G) :
    depth raw=G.1/2 := by rw [depth,dimension_of_decode h,List.length_replicate]

lemma canonical_ready (G : GraphInput) (r k : ℕ) (tape : BitString) (he : G.1%2=0)
    (ht : SelfReduction.GraphCount.randomBitsPolynomial.eval (estimateInput G.encode r k).length≤tape.length) :
    ready (pairBits (estimateInput G.encode r k) tape)=true := by
  have hd : dimension (pairBits (estimateInput G.encode r k) tape)=List.replicate G.1 true :=
    dimension_of_decode (by simp)
  apply (ready_iff _).mpr
  refine ⟨by simp,by simp [request,estimateInput],by simp,?_,?_⟩
  · simpa using ht
  · rw [hd,List.length_replicate]
    exact he

/-- Odd graph orders cannot enter the counting loop, including order one. -/
lemma canonical_odd (G : GraphInput) (r k : ℕ) (tape : BitString) (he : G.1%2≠0) :
    ready (pairBits (estimateInput G.encode r k) tape)=false := by
  have hd : dimension (pairBits (estimateInput G.encode r k) tape)=List.replicate G.1 true :=
    dimension_of_decode (by simp)
  simp [ready,even,hd,he]

/-- Every accepted raw input carries a genuine canonical graph of even order. -/
theorem accepted_input (raw : BitString) (hr : ready raw=true) :
    ∃G : GraphInput,G.encode=graph raw ∧dimension raw=List.replicate G.1 true ∧
      G.1≤size raw ∧G.1%2=0 ∧
      SelfReduction.GraphCount.randomBitsPolynomial.eval (size raw)≤(coins raw).length := by
  have hs := (ready_iff raw).mp hr
  obtain ⟨G,hG⟩ := Option.isSome_iff_exists.mp hs.2.2.1
  have hd := dimension_of_decode hG
  refine ⟨G,GraphInput.decode_some hG,hd,?_,?_,hs.2.2.2.1⟩
  · exact (GraphInput.decode_vertices_bound hG).trans (lengths raw).2.2.1
  · simpa only [hd,List.length_replicate] using hs.2.2.2.2

lemma canonical_bounds (G : GraphInput) (r k : ℕ) :
    G.1≤(estimateInput G.encode r k).length ∧r≤(estimateInput G.encode r k).length ∧
      k≤(estimateInput G.encode r k).length := by
  have hd := GraphInput.decode_vertices_bound (GraphInput.decode_encode G)
  simp only [estimateInput_length]
  omega
end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
