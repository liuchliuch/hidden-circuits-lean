import HiddenCircuits.GraphReduction.Runtime.PairEval.Input
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueWordQuery

namespace HiddenCircuits.GraphReduction.Runtime.PairEval.GraphFrontend
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
set_option maxHeartbeats 1000000

def graphInput (w : PairInput) (t s : ℕ) : GraphInput := monotoneGraphInput (fun i=>w.pairs.get i) w.source w.target s
def queryBits (w : PairInput) (t s : ℕ) : BitString := (graphInput w t s).encode

def input (w : PairInput) (t s : ℕ) : Store 81 := fun i =>
  if i.val=77 then pairInputBits w else if i.val=81 then List.replicate t true else if i.val=74 then List.replicate s true else []
def combine (w : PairInput) (t : ℕ) (low : Store 76) : Store 81 := fun i =>
  if h:i.val<77 then low ⟨i.val,h⟩ else if i.val=77 then pairInputBits w
  else if i.val=78 then List.replicate w.particles true else if i.val=79 then []
  else if i.val=80 then [] else List.replicate t true

def sampled (w : PairInput) (t s width : ℕ) : Store 81 := combine w t
  (PairedQuery.state width w.pairs.length s 0 (stateBits w.source) (stateBits w.target) (pairStream w.pairs) [] [])
def output (w : PairInput) (t s : ℕ) : Store 81 := combine w t
  (PairedQuery.state (2*w.particles) w.pairs.length s (graphInput w t s).1 (stateBits w.source) (stateBits w.target)
    (pairStream w.pairs) (monotoneDescriptor (fun i=>w.pairs.get i) w.source w.target s) (queryBits w t s))

def sampleEmbedding : Fin 18 ↪ Fin 82 where
  toFun i := (![77,78,69,70,73,67,74,57,58,59,60,61,62,63,64,66,68,71] : Fin 18 → Fin 82) i
  inj' := by decide +kernel
def pairedEmbedding : Fin 77 ↪ Fin 82 := Fin.castAddEmb 5
noncomputable def sample : OracleBlock 81 := rename Input.program sampleEmbedding
noncomputable def doubleWidth : OracleBlock 81 := seq (copyOn 78 65 66 (by decide) (by decide) (by decide))
  (copyOn 78 65 66 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 81 := seq sample (seq doubleWidth (rename PairedQuery.program pairedEmbedding))

lemma sample_executes (g : BitString → ℕ) (w : PairInput) (t s : ℕ) :
    ∃c,sample.Executes g (input w t s) (sampled w t s 0) c ∧ c≤40*(pairInputBits w).length+100 := by
  obtain ⟨c,hc,hb⟩ := Input.program_executes g w s
  refine ⟨c,?_,hb⟩
  apply rename_executes_to Input.program sampleEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · clear hc hb
    intro i hi
    fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim | exact (hi 4 rfl).elim | exact (hi 5 rfl).elim | exact (hi 12 rfl).elim | exact (hi 16 rfl).elim | exact (hi 6 rfl).elim

lemma sampled_width_update (w : PairInput) (t s a b : ℕ) :
    Function.update (sampled w t s a) (65:Fin 82) (List.replicate b true)=sampled w t s b := by
  funext i
  by_cases hi:i=65
  · subst i;rfl
  · have hv:i.val≠65 := by intro h;exact hi (Fin.ext h)
    simp only [Function.update_of_ne hi]
    by_cases hlo:i.val<77
    · simp only [sampled,combine,hlo,↓reduceDIte,PairedQuery.state,hv,if_false]
    · simp only [sampled,combine,hlo,↓reduceDIte]

lemma doubleWidth_executes (g : BitString → ℕ) (w : PairInput) (t s : ℕ) :
    doubleWidth.Executes g (sampled w t s 0) (sampled w t s (2*w.particles)) (10*w.particles+6) := by
  have h₁ : (copyOn (78:Fin 82) 65 66 (by decide) (by decide) (by decide)).Executes g
      (sampled w t s 0) (sampled w t s w.particles) (5*w.particles+2) := by
    have he := copyOn_executes g (78:Fin 82) 65 66 (by decide) (by decide) (by decide) (sampled w t s 0) rfl
    change (copyOn (78:Fin 82) 65 66 (by decide) (by decide) (by decide)).Executes g (sampled w t s 0)
      (Function.update (sampled w t s 0) 65 (List.replicate w.particles true++[])) (5*(List.replicate w.particles true).length+2) at he
    simpa only [List.append_nil,List.length_replicate,sampled_width_update] using he
  have h₂ : (copyOn (78:Fin 82) 65 66 (by decide) (by decide) (by decide)).Executes g
      (sampled w t s w.particles) (sampled w t s (2*w.particles)) (5*w.particles+2) := by
    have he := copyOn_executes g (78:Fin 82) 65 66 (by decide) (by decide) (by decide) (sampled w t s w.particles) rfl
    change (copyOn (78:Fin 82) 65 66 (by decide) (by decide) (by decide)).Executes g (sampled w t s w.particles)
      (Function.update (sampled w t s w.particles) 65 (List.replicate w.particles true++List.replicate w.particles true))
      (5*(List.replicate w.particles true).length+2) at he
    simpa only [←List.replicate_add,List.length_replicate,sampled_width_update,←two_mul] using he
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

theorem program_executes (g : BitString → ℕ) (w : PairInput) (t s : ℕ) :
    ∃c,program.Executes g (input w t s) (output w t s) c ∧
      c≤40*(pairInputBits w).length+100+10*w.particles+
        PairedQuery.time.eval (w.particles+w.pairs.length+s)+10 := by
  obtain ⟨a,ha,hab⟩ := sample_executes g w t s
  have hd := doubleWidth_executes g w t s
  obtain ⟨b,hb,hbb⟩ := PairedQuery.program_polynomial g w.pairs w.source w.target s
  have hp : (rename PairedQuery.program pairedEmbedding).Executes g (sampled w t s (2*w.particles)) (output w t s) b := by
    apply rename_executes_to PairedQuery.program pairedEmbedding g hb
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hb hbb
      intro i hi
      have hlow:¬i.val<77 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
      simp only [sampled,output,combine,hlow,↓reduceDIte]
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hd hp),by omega⟩
noncomputable def time : Polynomial ℕ := 50*X+PairedQuery.time.comp (2*X)+110
lemma program_polynomial (g : BitString→ℕ) (w : PairInput) (t s : ℕ) :
    ∃c,program.Executes g (input w t s) (output w t s) c ∧ c≤time.eval ((pairInputBits w).length+t+s) := by
  obtain ⟨c,hc,hb⟩:=program_executes g w t s
  refine ⟨c,hc,hb.trans ?_⟩
  have hin:=pairInputBits_length_lower w
  have hm:=polynomial_nat_eval_mono PairedQuery.time (show w.particles+w.pairs.length+s≤2*((pairInputBits w).length+t+s) by omega)
  dsimp only at hm
  simp only [time,eval_add,eval_mul,eval_ofNat,eval_X,eval_comp]
  omega
lemma sample_queryFree : sample.QueryFree := rename_queryFree _ _ Input.program_queryFree
end HiddenCircuits.GraphReduction.Runtime.PairEval.GraphFrontend
