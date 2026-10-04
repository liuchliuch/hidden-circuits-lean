/- widened actual raw-word sampling and supplied-unit frontend. -/
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSamplePolynomial
import HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitPairedQuery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSampleNoQuery

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitWordQuery
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1000000

def graphInput (w : WordInstance) (t s : ℕ) : GraphInput := unitGraphInput (fun i=>(sampleWord w.word t).get i) w.source w.target s
def queryBits (w : WordInstance) (t s : ℕ) : BitString := UnitSuppliedQuery.bits (sampleWord w.word t) w.source w.target s
def descriptor (w : WordInstance) (t s : ℕ) : BitString := unitDescriptor (fun i=>(sampleWord w.word t).get i) w.source w.target s

def input (w : WordInstance) (t s : ℕ) : Store 119 := fun i =>
  if i.val=115 then wordBits w else if i.val=119 then List.replicate t true else if i.val=74 then List.replicate s true else []
def combine (w : WordInstance) (t : ℕ) (low : Store 114) : Store 119 := fun i =>
  if h:i.val<115 then low ⟨i.val,h⟩ else if i.val=115 then wordBits w
  else if i.val=116 then List.replicate w.particles true else if i.val=117 then encodeBitList (w.word.map letterBits)
  else if i.val=118 then List.replicate w.word.length true else List.replicate t true

def state (w : WordInstance) (t s width count : ℕ) (desc out : BitString) : Store 119 := combine w t
  (UnitPairedQuery.state width (sampleWord w.word t).length s count (stateBits w.source) (stateBits w.target)
    (pairStream (sampleWord w.word t)) desc out)
def sampled (w : WordInstance) (t s width : ℕ) : Store 119 := state w t s width 0 [] []
def output (w : WordInstance) (t s : ℕ) : Store 119 :=
  state w t s (2*w.particles) (graphInput w t s).1 (descriptor w t s) (queryBits w t s)

def sampleEmbedding : Fin 18 ↪ Fin 120 where
  toFun i := (![115,116,69,70,117,118,119,57,58,59,60,61,73,62,63,64,67,66] : Fin 18 → Fin 120) i
  inj' := by decide +kernel
def pairedEmbedding : Fin 115 ↪ Fin 120 := Fin.castAddEmb 5
noncomputable def sample : OracleBlock 119 := rename WordSample.program sampleEmbedding
noncomputable def doubleWidth : OracleBlock 119 := seq (copyOn 116 65 66 (by decide) (by decide) (by decide))
  (copyOn 116 65 66 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 119 := seq sample (seq doubleWidth (rename UnitPairedQuery.program pairedEmbedding))

lemma sample_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,sample.Executes g (input w t s) (sampled w t s 0) c ∧ c≤WordSample.time.eval ((wordBits w).length+t) := by
  obtain ⟨c,hc,hb⟩ := WordSample.program_polynomial g w t
  refine ⟨c,?_,hb⟩
  apply rename_executes_to WordSample.program sampleEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · clear hc hb
    intro i hi
    fin_cases i <;> first | rfl | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim | exact (hi 4 rfl).elim | exact (hi 5 rfl).elim | exact (hi 12 rfl).elim | exact (hi 16 rfl).elim

lemma sampled_width_update (w : WordInstance) (t s a b : ℕ) :
    Function.update (sampled w t s a) (65:Fin 120) (List.replicate b true)=sampled w t s b := by
  funext i
  by_cases hi:i=65
  · subst i;rfl
  · have hv:i.val≠65 := by intro h;exact hi (Fin.ext h)
    simp only [Function.update_of_ne hi]
    by_cases hlo:i.val<115
    · simp [sampled,state,combine,hlo,UnitPairedQuery.state,PairedQuery.state,hv]
    · simp only [sampled,state,combine,hlo,↓reduceDIte]

lemma doubleWidth_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    doubleWidth.Executes g (sampled w t s 0) (sampled w t s (2*w.particles)) (10*w.particles+6) := by
  have h₁ : (copyOn (116:Fin 120) 65 66 (by decide) (by decide) (by decide)).Executes g
      (sampled w t s 0) (sampled w t s w.particles) (5*w.particles+2) := by
    have he := copyOn_executes g (116:Fin 120) 65 66 (by decide) (by decide) (by decide) (sampled w t s 0) rfl
    change (copyOn (116:Fin 120) 65 66 (by decide) (by decide) (by decide)).Executes g (sampled w t s 0)
      (Function.update (sampled w t s 0) 65 (List.replicate w.particles true++[])) (5*(List.replicate w.particles true).length+2) at he
    simpa only [List.append_nil,List.length_replicate,sampled_width_update] using he
  have h₂ : (copyOn (116:Fin 120) 65 66 (by decide) (by decide) (by decide)).Executes g
      (sampled w t s w.particles) (sampled w t s (2*w.particles)) (5*w.particles+2) := by
    have he := copyOn_executes g (116:Fin 120) 65 66 (by decide) (by decide) (by decide) (sampled w t s w.particles) rfl
    change (copyOn (116:Fin 120) 65 66 (by decide) (by decide) (by decide)).Executes g (sampled w t s w.particles)
      (Function.update (sampled w t s w.particles) 65 (List.replicate w.particles true++List.replicate w.particles true))
      (5*(List.replicate w.particles true).length+2) at he
    simpa only [←List.replicate_add,List.length_replicate,sampled_width_update,←two_mul] using he
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

theorem program_runs (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,program.Executes g (input w t s) (output w t s) c ∧
      c≤WordSample.time.eval ((wordBits w).length+t)+10*w.particles+
        UnitPairedQuery.time.eval (w.particles+(sampleWord w.word t).length+s)+10 := by
  obtain ⟨a,ha,hab⟩ := sample_executes g w t s
  have hd := doubleWidth_executes g w t s
  obtain ⟨b,hb,hbb⟩ := UnitPairedQuery.program_executes g (sampleWord w.word t) w.source w.target s
  have hp : (rename UnitPairedQuery.program pairedEmbedding).Executes g (sampled w t s (2*w.particles)) (output w t s) b := by
    apply rename_executes_to UnitPairedQuery.program pairedEmbedding g hb
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hb hbb
      intro i hi
      have hlow:¬i.val<115 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
      simp only [sampled,output,state,combine,hlow,↓reduceDIte]
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hd hp),by omega⟩

noncomputable def time : Polynomial ℕ := WordSample.time+10*X+UnitPairedQuery.time.comp (3*(X+1)^2)+10

theorem program_polynomial (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,program.Executes g (input w t s) (output w t s) c ∧ c≤time.eval ((wordBits w).length+t+s) := by
  obtain ⟨c,hc,hb⟩ := program_runs g w t s
  refine ⟨c,hc,hb.trans ?_⟩
  let N := (wordBits w).length+t+s
  have hin := wordBits_length_lower w
  have hp : w.particles≤N := by dsimp [N];omega
  have hn : w.word.length≤N := by dsimp [N];omega
  have ht : t≤N := by dsimp [N];omega
  have hs : s≤N := by dsimp [N];omega
  have hh : w.word.length*(t+1)≤N*(N+1) := Nat.mul_le_mul hn (by omega)
  have hq : w.particles+(sampleWord w.word t).length+s≤3*(N+1)^2 := by
    rw [sampleWord_length]
    nlinarith
  have ha := polynomial_nat_eval_mono WordSample.time (show (wordBits w).length+t≤N by dsimp[N];omega)
  have hb := polynomial_nat_eval_mono UnitPairedQuery.time hq
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_comp,eval_pow,eval_one]
  dsimp only [N] at *
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ WordSample.program_queryFree)
  (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
    (rename_queryFree _ _ UnitPairedQuery.program_queryFree))

theorem program_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,program.Executes g (input w t s) (state w t s (2*w.particles) (graphInput w t s).1 (descriptor w t s) (queryBits w t s)) c ∧
      c≤time.eval ((wordBits w).length+t+s) := program_polynomial g w t s
end HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitWordQuery
