import HiddenCircuits.Complexity.PairPreprocess
import HiddenCircuits.Complexity.OraclePrecompose
import HiddenCircuits.Complexity.GraphVerifier.PaddedMatchingFinalRuntime

/-! Machine-grounded #P closure under an actual polynomial graph-input compiler. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingPullback
open OracleBlock Polynomial
variable {k : ℕ}

def verifier (f : BitString → BitString) (xs : BitString) : Bool :=
  PaddedMatching.verifier (PairPreprocess.mapFirst f xs)
noncomputable def program (B : OracleBlock k) : OracleBlock (k+51) :=
  precompose (resize (PairPreprocess.program B) (by omega))
    (resize PaddedMatchingRuntime.verifierBlock (by omega))
noncomputable def pairSize (size : Polynomial ℕ) : Polynomial ℕ := 2*size+X+1
noncomputable def time (p size : Polynomial ℕ) : Polynomial ℕ :=
  precomposeTime (k:=k+51) (PairPreprocess.time (k:=k) p size) (2000*(X+1)^4) (pairSize size)

theorem pair_size (f : BitString → BitString) (size : Polynomial ℕ)
    (hs : ∀x,(f x).length≤size.eval x.length) (xs : BitString) :
    (PairPreprocess.mapFirst f xs).length≤(pairSize size).eval xs.length := by
  rw [PairPreprocess.mapFirst,parse_spec]
  cases hok:(parse xs).ok with
  | false => simp [hok]
  | true =>
    simp only [hok,if_true]
    have hl:=Runtime.parse_lengths xs
    have hp:=(hs (parse xs).left).trans (polynomial_nat_eval_mono size hl.1)
    dsimp only at hp
    simp only [pairBits_length,pairSize,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
    omega

theorem program_executes (B : OracleBlock k) (f : BitString → BitString) (p size : Polynomial ℕ)
    (hB : ∀x,∃s c,B.Executes (fun _=>0) (Function.update (fun _=>[]) 0 x) s c ∧s 0=f x∧c≤p.eval x.length)
    (hsize : ∀x,(f x).length≤size.eval x.length) (xs : BitString) :
    ∃s c,(program B).Executes (fun _=>0) (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=Computability.encodeBool (verifier f xs) ∧c≤(time (k:=k) p size).eval xs.length := by
  apply precompose_executes _ _ (fun _=>0) (PairPreprocess.mapFirst f)
    (fun x=>Computability.encodeBool (verifier f x)) (PairPreprocess.time (k:=k) p size) (2000*(X+1)^4) (pairSize size)
  · intro x
    obtain ⟨s,c,hc,ho,hb⟩:=PairPreprocess.program_executes B (fun _=>0) f p size hB hsize x
    obtain ⟨t,ht,he⟩:=resize_executes _ (show k+4≤k+51 by omega) (fun _=>0) x s c hc
    exact ⟨t,c,ht,he.trans ho,hb⟩
  · exact pair_size f size hsize
  · intro x
    obtain ⟨s,c,hc,ho,hb⟩:=PaddedMatchingRuntime.verifierBlock_executes (PairPreprocess.mapFirst f x)
    obtain ⟨t,ht,he⟩:=resize_executes _ (show 47≤k+51 by omega) (fun _=>0) _ s c hc
    refine ⟨t,c,ht,he.trans ho,?_⟩
    simpa only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one] using hb

lemma program_queryFree (B : OracleBlock k) (hB:B.QueryFree) : (program B).QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ (PairPreprocess.program_queryFree B hB))
    (seq_queryFree _ _ (cleanup_queryFree _) (rename_queryFree _ _ PaddedMatchingRuntime.verifierBlock_queryFree))

theorem polyVerifier (B : OracleBlock k) (hB:B.QueryFree) (f : BitString → BitString) (p size : Polynomial ℕ)
    (hrun : ∀x,∃s c,B.Executes (fun _=>0) (Function.update (fun _=>[]) 0 x) s c ∧s 0=f x∧c≤p.eval x.length)
    (hsize : ∀x,(f x).length≤size.eval x.length) : PolyVerifier (verifier f) :=
  polyVerifier_of_block _ (program B) (program_queryFree B hB) (time (k:=k) p size)
    (program_executes B f p size hrun hsize)

theorem certificateCount_comp (f : BitString → BitString) (x : BitString) (m : ℕ) :
    certificateCount (verifier f) x m=certificateCount PaddedMatching.verifier (f x) m := by
  simp only [certificateCount,verifier,PairPreprocess.mapFirst,unpair_pairBits]

theorem sharpP_of_graph_compiler (B : OracleBlock k) (hB:B.QueryFree)
    (f : BitString → BitString) (p size : Polynomial ℕ)
    (hrun : ∀x,∃s c,B.Executes (fun _=>0) (Function.update (fun _=>[]) 0 x) s c ∧s 0=f x∧c≤p.eval x.length)
    (hsize : ∀x,(f x).length≤size.eval x.length) : SharpP (GraphInput.perfectMatchingProblem ∘ f) := by
  refine ⟨size*size,verifier f,polyVerifier B hB f p size hrun hsize,?_⟩
  intro x
  rw [certificateCount_comp]
  apply (PaddedMatching.certificateCount_eq (f x) _ ?_).symm
  intro G hg
  have hn: G.1≤size.eval x.length := (GraphInput.decode_vertices_bound hg).trans (hsize x)
  simpa only [eval_mul] using Nat.mul_le_mul hn hn

end HiddenCircuits.Complexity.GraphVerifier.MatchingPullback
