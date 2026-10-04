import HiddenCircuits.GraphReduction.Runtime.EndpointGraphEmitter

/-! All-raw endpoint compiler: validate the actual endpoint arrays, emit their
bipartite adjacency matrix, map malformed inputs to a fixed zero-count graph,
and leave only canonical graph bytes. -/
namespace HiddenCircuits.GraphReduction.Runtime.EndpointGraph
open Complexity OracleBlock Approximation MonotoneEndpointEncoding Polynomial
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
noncomputable abbrev EP := SamplerRuntime.EndpointParser.program

def parsed (xs : BitString) : Store 39 := fun q =>
  if q.val=0 then xs else if q.val=1 then (SamplerRuntime.EndpointParser.first xs).left
  else if q.val=2 then (SamplerRuntime.EndpointParser.second xs).left
  else if q.val=3 then (SamplerRuntime.EndpointParser.third xs).left
  else if q.val=4 then [SamplerRuntime.EndpointParser.valid xs] else []
def parserMap : Fin 36 ↪ Fin 40 := Fin.castAddEmb 4
noncomputable def parse : OracleBlock 39 := rename EP parserMap
noncomputable def reject : OracleBlock 39 := seq (push 7 false) (seq (push 7 false) (seq (push 7 true) (push 7 true)))
noncomputable def valid : OracleBlock 39 := seq prepare emit
noncomputable def select : OracleBlock 39 := branchPop 4 reject reject valid
noncomputable def work : OracleBlock 39 := seq parse select
noncomputable def program : OracleBlock 39 := seq work (cleanResult 7 35 (by decide) (by decide))
noncomputable def workTime : Polynomial ℕ := SamplerRuntime.EndpointParser.time+7000*(X+1)^4+2
noncomputable def time : Polynomial ℕ := 45*workTime+44*X+135
noncomputable def size : Polynomial ℕ := 8*(X+1)^2

lemma parse_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c, parse.Executes g (Function.update (fun _ => []) 0 xs) (parsed xs) c ∧
      c ≤ SamplerRuntime.EndpointParser.time.eval xs.length := by
  obtain ⟨c,hc,hb⟩ := SamplerRuntime.EndpointParser.program_executes g xs
  refine ⟨c,?_,hb⟩
  apply rename_executes_to EP parserMap g hc
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq
    have hn : ¬q.val<36 := by intro h;exact hq ⟨q.val,h⟩ (Fin.ext rfl)
    have h0 : q≠0 := by intro h;subst q;norm_num at hn
    simp [parsed,show q.val≠0 by omega,show q.val≠1 by omega,show q.val≠2 by omega,
      show q.val≠3 by omega,show q.val≠4 by omega,Function.update_of_ne h0]
lemma parsed_fields {xs : BitString} {E : Input} (h : decode xs=some E) :
    Function.update (parsed xs) (4:Fin 40) []=preState xs E.2 := by
  have hf := SamplerRuntime.EndpointParser.fields_of_decode h
  funext q;fin_cases q <;> first | rfl | exact hf.1 | exact hf.2.1 | exact hf.2.2
lemma parsed_flag (xs : BitString) : parsed xs 4=[(decode xs).isSome] := by
  change [SamplerRuntime.EndpointParser.valid xs]=_
  rw [SamplerRuntime.EndpointParser.valid_eq_decode]

lemma reject_executes (g : BitString → ℕ) (s : Store 39) (h7 : s 7=[]) :
    reject.Executes g s (Function.update s 7 rejectedGraph.encode) 10 := by
  let s1 := Function.update s (7:Fin 40) [false]
  let s2 := Function.update s (7:Fin 40) [false,false]
  let s3 := Function.update s (7:Fin 40) [true,false,false]
  have h1 : (push (7:Fin 40) false).Executes g s s1 1 := by simpa [s1,h7] using push_executes g (7:Fin 40) false s
  have h2 : (push (7:Fin 40) false).Executes g s1 s2 1 := by simpa [s1,s2] using push_executes g (7:Fin 40) false s1
  have h3 : (push (7:Fin 40) true).Executes g s2 s3 1 := by simpa [s2,s3] using push_executes g (7:Fin 40) true s2
  have h4 : (push (7:Fin 40) true).Executes g s3 (Function.update s 7 rejectedGraph.encode) 1 := by
    simpa [s3,rejectedGraph_bits] using push_executes g (7:Fin 40) true s3
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4))

lemma valid_executes {xs : BitString} {E : Input} (h : decode xs=some E) (g : BitString → ℕ) :
    ∃c, valid.Executes g (preState xs E.2) (Function.update (ready E.2) 7 (graph E).encode) c ∧
      c ≤ 6000*(xs.length+1)^4 := by
  have hp := prepare_executes g xs E.2
  obtain ⟨c,hc,hcb⟩ := emit_polynomial h g
  refine ⟨_,seq_executes _ _ g hp hc,?_⟩
  have hn := MonotoneEndpointEncoding.size_le_of_decode h
  have hd := data_length_of_decode h
  have hb : xs.length+16*E.1+6*(encodeBitList (rows E.2.lo)).length+6*(encodeBitList (rows E.2.hi)).length+30 ≤ 29*xs.length+30 := by omega
  apply (Nat.add_le_add_right (Nat.add_le_add hb hcb) 2).trans
  ring_nf
  omega

lemma select_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s c, select.Executes g (parsed xs) s c ∧ s 7=compiledBits xs ∧ c ≤ 7000*(xs.length+1)^4 := by
  have hp : 1 ≤ (xs.length+1)^4 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) _)
  cases h:decode xs with
  | none =>
    have hf : parsed xs 4=false::[] := by rw [parsed_flag,h];rfl
    have hr := reject_executes g (Function.update (parsed xs) (4:Fin 40) []) rfl
    refine ⟨_,12,branchPop_false (4:Fin 40) reject reject valid g hf hr,?_,by omega⟩
    simp only [Function.update_self,compiledBits,h]
  | some E =>
    have hf : parsed xs 4=true::[] := by rw [parsed_flag,h];rfl
    obtain ⟨c,hc,hcb⟩ := valid_executes h g
    have hc' : valid.Executes g (Function.update (parsed xs) (4:Fin 40) []) (Function.update (ready E.2) 7 (graph E).encode) c := by
      rw [parsed_fields h];exact hc
    refine ⟨_,c+2,branchPop_true (4:Fin 40) reject reject valid g hf hc',?_,by omega⟩
    simp only [Function.update_self,compiledBits,h]

lemma work_executes (g : BitString → ℕ) (xs : BitString) :
    ∃s c, work.Executes g (Function.update (fun _ => []) 0 xs) s c ∧ s 7=compiledBits xs ∧ c ≤ workTime.eval xs.length := by
  obtain ⟨a,ha,hab⟩ := parse_executes g xs
  obtain ⟨s,b,hb,ho,hbb⟩ := select_executes g xs
  refine ⟨s,_,seq_executes _ _ g ha hb,ho,?_⟩
  simp only [workTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  omega

theorem program_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c, program.Executes g (Function.update (fun _ => []) 0 xs) (Function.update (fun _ => []) 0 (compiledBits xs)) c ∧
      c ≤ time.eval xs.length := by
  obtain ⟨s,c,hc,ho,hcb⟩ := work_executes g xs
  have hi : ∀q : Fin 40,(Function.update (fun _ => []) 0 xs q).length ≤ xs.length := by
    intro q;by_cases hq:q=0 <;> simp [Function.update_apply,hq]
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes g (7:Fin 40) 35 (by decide) (by decide) (by decide)
    s (xs.length+c) (hc.stack_bound hi)
  rw [ho] at hd
  refine ⟨_,seq_executes _ _ g hc hd,?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega
lemma reject_queryFree : reject.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (rename_queryFree _ _ SamplerRuntime.EndpointParser.program_queryFree)
    (branchPop_queryFree _ _ _ _ reject_queryFree reject_queryFree (seq_queryFree _ _ prepare_queryFree emit_queryFree)))
  (cleanResult_queryFree _ _ _ _)
end HiddenCircuits.GraphReduction.Runtime.EndpointGraph
