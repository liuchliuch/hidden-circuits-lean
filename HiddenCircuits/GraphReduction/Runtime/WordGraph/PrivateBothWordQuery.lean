import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueWordQuery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivateBothPairedQuery

/-! Canonical word inputs physically emit both representations with each graph query. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivateBothWordQuery
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1000000

def graphInput (w : WordInstance) (t s : ℕ) : GraphInput :=
  CliqueEmitter.graphInput true (fun i => (sampleWord w.word t).get i) w.source w.target (2*s)
def pairedBits {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) : BitString :=
  PrivateBothQuery.bits (fun i => ps.get i) S T s
def queryBits (w : WordInstance) (t s : ℕ) : BitString :=
  pairedBits (sampleWord w.word t) w.source w.target (2*s)
noncomputable abbrev pairedProgram := PrivateBothPairedQuery.program
noncomputable abbrev pairedTime := PrivateBothPairedQuery.time
lemma paired_executes {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    ∃ c, pairedProgram.Executes g
      (PairedQuery.state (2*p) ps.length s 0 (stateBits S) (stateBits T) (pairStream ps) [] [])
      (PairedQuery.state (2*p) ps.length s (CliqueEmitter.graphInput true (fun i => ps.get i) S T s).1
        (stateBits S) (stateBits T) (pairStream ps) (CliqueEmitter.descriptor true (fun i => ps.get i) S T s)
        (pairedBits ps S T s)) c ∧ c ≤ pairedTime.eval (p+ps.length+s) :=
  PrivateBothPairedQuery.program_polynomial g ps S T s
lemma paired_queryFree : pairedProgram.QueryFree := PrivateBothPairedQuery.program_queryFree
abbrev input := WordQuery.input

def output (w : WordInstance) (t s : ℕ) : Store 81 := WordQuery.combine w t
  (PairedQuery.state (2*w.particles) (sampleWord w.word t).length (2*s) (graphInput w t s).1
    (stateBits w.source) (stateBits w.target) (pairStream (sampleWord w.word t))
    (CliqueEmitter.descriptor true (fun i => (sampleWord w.word t).get i) w.source w.target (2*s))
    (queryBits w t s))
noncomputable abbrev doubleProbe := CliqueWordQuery.doubleProbe
noncomputable def program : OracleBlock 81 := seq WordQuery.sample
  (seq WordQuery.doubleWidth (seq doubleProbe (rename pairedProgram WordQuery.pairedEmbedding)))
noncomputable def time : Polynomial ℕ := WordSample.time+21*X+pairedTime.comp (4*(X+1)^2)+21

theorem program_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,(program).Executes g (input w t s) (output w t s) c ∧ c≤(time).eval ((wordBits w).length+t+s) := by
  obtain ⟨a,ha,hab⟩ := WordQuery.sample_executes g w t s
  have hd := WordQuery.doubleWidth_executes g w t s
  have hp := CliqueWordQuery.doubleProbe_executes g w t s (2*w.particles)
  obtain ⟨b,hb,hbb⟩ := paired_executes g (sampleWord w.word t) w.source w.target (2*s)
  have hq : (rename (pairedProgram) WordQuery.pairedEmbedding).Executes g
      (WordQuery.sampled w t (2*s) (2*w.particles)) (output w t s) b := by
    apply rename_executes_to (pairedProgram) WordQuery.pairedEmbedding g hb
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hb hbb
      intro i hi
      have hlo:¬i.val<77:=by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
      simp only [WordQuery.sampled,output,WordQuery.combine,hlo,↓reduceDIte]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hd (seq_executes _ _ g hp hq)),?_⟩
  let N:=(wordBits w).length+t+s
  have hin:=wordBits_length_lower w
  have hpN:w.particles≤N:=by dsimp[N];omega
  have hn:w.word.length≤N:=by dsimp[N];omega
  have ht:t≤N:=by dsimp[N];omega
  have hs:s≤N:=by dsimp[N];omega
  have hh:w.word.length*(t+1)≤N*(N+1):=Nat.mul_le_mul hn (by omega)
  have hqin:w.particles+(sampleWord w.word t).length+2*s≤4*(N+1)^2:=by rw [sampleWord_length];nlinarith
  have hsamp:=polynomial_nat_eval_mono WordSample.time (show (wordBits w).length+t≤N by dsimp[N];omega)
  have hpair:=polynomial_nat_eval_mono (pairedTime) hqin
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_comp,eval_pow,eval_one]
  dsimp only [N] at *
  omega

lemma program_queryFree : (program).QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ WordSample.program_queryFree)
  (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
    (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (clear_queryFree _)))
      (rename_queryFree _ _ (paired_queryFree))))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivateBothWordQuery
