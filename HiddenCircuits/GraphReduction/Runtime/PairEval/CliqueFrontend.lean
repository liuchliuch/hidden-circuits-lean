import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphFrontend
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliquePairedSize
import HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivatePairedSuppliedQuery

namespace HiddenCircuits.GraphReduction.Runtime.PairEval.CliqueFrontend
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
set_option maxHeartbeats 1000000
inductive Kind where
  | unit
  | privateGraph
  | suppliedPrivate
  deriving DecidableEq

def mode : Kind → Bool
  | .unit => false
  | .privateGraph => true
  | .suppliedPrivate => true

def graphInput (kind : Kind) (w : PairInput) (t s : ℕ) : GraphInput :=
  CliqueEmitter.graphInput (mode kind) (fun i=>w.pairs.get i) w.source w.target (2*s)
def pairedBits (kind : Kind) {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) : BitString :=
  match kind with
  | .suppliedPrivate => PrivateSuppliedQuery.bits (fun i=>ps.get i) S T s
  | _ => (CliqueEmitter.graphInput (mode kind) (fun i=>ps.get i) S T s).encode
def queryBits (kind : Kind) (w : PairInput) (t s : ℕ) : BitString :=
  pairedBits kind w.pairs w.source w.target (2*s)
noncomputable def pairedProgram : Kind → OracleBlock 76
  | .suppliedPrivate => PrivatePairedSuppliedQuery.program
  | k => CliquePairedQuery.program (mode k)
noncomputable def pairedTime : Kind → Polynomial ℕ
  | .suppliedPrivate => PrivatePairedSuppliedQuery.time
  | _ => CliquePairedQuery.time
lemma paired_executes (kind : Kind) {p : ℕ} (g : BitString→ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃c,(pairedProgram kind).Executes g (PairedQuery.state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (PairedQuery.state (2*p) ps.length s (CliqueEmitter.graphInput (mode kind) (fun i=>ps.get i) S T s).1
        (stateBits S) (stateBits T) (pairStream ps) (CliqueEmitter.descriptor (mode kind) (fun i=>ps.get i) S T s)
        (pairedBits kind ps S T s)) c ∧ c≤(pairedTime kind).eval (p+ps.length+s) := by
  cases kind
  · exact CliquePairedQuery.program_polynomial g false ps S T s
  · exact CliquePairedQuery.program_polynomial g true ps S T s
  · exact PrivatePairedSuppliedQuery.program_polynomial g ps S T s
lemma paired_queryFree (kind : Kind) : (pairedProgram kind).QueryFree := by
  cases kind
  · exact CliquePairedQuery.program_queryFree false
  · exact CliquePairedQuery.program_queryFree true
  · exact PrivatePairedSuppliedQuery.program_queryFree
abbrev input := GraphFrontend.input

def output (kind : Kind) (w : PairInput) (t s : ℕ) : Store 81 := GraphFrontend.combine w t
  (PairedQuery.state (2*w.particles) w.pairs.length (2*s) (graphInput kind w t s).1 (stateBits w.source) (stateBits w.target)
    (pairStream w.pairs) (CliqueEmitter.descriptor (mode kind) (fun i=>w.pairs.get i) w.source w.target (2*s)) (queryBits kind w t s))
noncomputable def doubleProbe : OracleBlock 81 := seq (copyOn 74 75 76 (by decide) (by decide) (by decide))
  (seq (copyOn 75 74 76 (by decide) (by decide) (by decide)) (clear 75))
noncomputable def program (kind : Kind) : OracleBlock 81 := seq GraphFrontend.sample
  (seq GraphFrontend.doubleWidth (seq doubleProbe (rename (pairedProgram kind) GraphFrontend.pairedEmbedding)))
noncomputable def time (kind : Kind) : Polynomial ℕ := 61*X+(pairedTime kind).comp (4*(X+1)^2)+121

lemma sampled_samples_update (w : PairInput) (t s width next : ℕ) :
    Function.update (GraphFrontend.sampled w t s width) (74:Fin 82) (List.replicate next true)=GraphFrontend.sampled w t next width := by
  funext i
  by_cases hi:i=74
  · subst i;rfl
  · have hv:i.val≠74 := by intro h;exact hi (Fin.ext h)
    simp only [Function.update_of_ne hi]
    by_cases hlo:i.val<77
    · simp only [GraphFrontend.sampled,GraphFrontend.combine,hlo,↓reduceDIte,PairedQuery.state,hv,if_false]
    · simp only [GraphFrontend.sampled,GraphFrontend.combine,hlo,↓reduceDIte]

lemma doubleProbe_executes (g : BitString → ℕ) (w : PairInput) (t s width : ℕ) :
    doubleProbe.Executes g (GraphFrontend.sampled w t s width) (GraphFrontend.sampled w t (2*s) width) (11*s+9) := by
  let start := GraphFrontend.sampled w t s width
  let a := Function.update start (75:Fin 82) (List.replicate s true)
  let b := Function.update (GraphFrontend.sampled w t (2*s) width) (75:Fin 82) (List.replicate s true)
  have h₁ : (copyOn (74:Fin 82) 75 76 (by decide) (by decide) (by decide)).Executes g start a (5*s+2) := by
    simpa [a,start,GraphFrontend.sampled,GraphFrontend.combine,PairedQuery.state] using copyOn_executes g (74:Fin 82) 75 76 (by decide) (by decide) (by decide) start rfl
  have h₂ : (copyOn (75:Fin 82) 74 76 (by decide) (by decide) (by decide)).Executes g a b (5*s+2) := by
    have hc := copyOn_executes g (75:Fin 82) 74 76 (by decide) (by decide) (by decide) a rfl
    have he : Function.update a (74:Fin 82) (a 75++a 74)=b := by
      change Function.update (Function.update start 75 (List.replicate s true)) 74 (List.replicate s true++List.replicate s true)=b
      rw [←List.replicate_add,←two_mul,Function.update_comm (by decide : (75:Fin 82)≠74)]
      rw [show start=GraphFrontend.sampled w t s width from rfl,sampled_samples_update]
    rw [he] at hc
    simpa [a] using hc
  have h₃ : (clear (75:Fin 82)).Executes g b (GraphFrontend.sampled w t (2*s) width) (s+1) := by
    have hc := clear_executes g (75:Fin 82) b
    have he : Function.update b 75 []=GraphFrontend.sampled w t (2*s) width := by
      change Function.update (Function.update (GraphFrontend.sampled w t (2*s) width) (75:Fin 82) (List.replicate s true)) 75 []=_
      rw [Function.update_idem]
      exact Function.update_eq_self _ _
    rw [he] at hc
    simpa [b] using hc
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃) using 1 <;> omega

theorem program_executes (kind : Kind) (g : BitString → ℕ) (w : PairInput) (t s : ℕ) :
    ∃c,(program kind).Executes g (input w t s) (output kind w t s) c ∧ c≤(time kind).eval ((pairInputBits w).length+t+s) := by
  obtain ⟨a,ha,hab⟩ := GraphFrontend.sample_executes g w t s
  have hd := GraphFrontend.doubleWidth_executes g w t s
  have hp := doubleProbe_executes g w t s (2*w.particles)
  obtain ⟨b,hb,hbb⟩ := paired_executes kind g w.pairs w.source w.target (2*s)
  have hq : (rename (pairedProgram kind) GraphFrontend.pairedEmbedding).Executes g
      (GraphFrontend.sampled w t (2*s) (2*w.particles)) (output kind w t s) b := by
    apply rename_executes_to (pairedProgram kind) GraphFrontend.pairedEmbedding g hb
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hb hbb
      intro i hi
      have hlo:¬i.val<77:=by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
      simp only [GraphFrontend.sampled,output,GraphFrontend.combine,hlo,↓reduceDIte]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hd (seq_executes _ _ g hp hq)),?_⟩
  let N:=(pairInputBits w).length+t+s
  have hin:=pairInputBits_length_lower w
  have hpN:w.particles≤N:=by dsimp[N];omega
  have hn:w.pairs.length≤N:=by dsimp[N];omega
  have hs:s≤N:=by dsimp[N];omega
  have hqin:w.particles+w.pairs.length+2*s≤4*(N+1)^2:=by nlinarith
  have hpair:=polynomial_nat_eval_mono (pairedTime kind) hqin
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_comp,eval_pow,eval_one]
  dsimp only [N] at *
  omega

lemma program_queryFree (kind : Kind) : (program kind).QueryFree := seq_queryFree _ _
  GraphFrontend.sample_queryFree
  (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
    (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (clear_queryFree _)))
      (rename_queryFree _ _ (paired_queryFree kind))))
end HiddenCircuits.GraphReduction.Runtime.PairEval.CliqueFrontend
