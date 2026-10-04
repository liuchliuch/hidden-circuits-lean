import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointProgram

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

lemma step_bounds (R : List VertexRecord) (i k : ℕ) (A : Accum) :
    (step R i k A).count≤A.count+1 ∧ (step R i k A).lows.length≤A.lows.length+2*R.length+2 ∧
      (step R i k A).highs.length≤A.highs.length+2*R.length+2 := by
  have hu:=countValue_le false true R i
  have hv:=countValue_le true true R i
  unfold step
  split_ifs
  · have hmin:min (countValue false true R i) (countValue true true R i)≤R.length:=min_le_of_left_le hu
    have hmax:max (countValue false true R i) (countValue true true R i)≤R.length:=max_le hu hv
    simp only [emitValues,List.length_append,List.length_reverse,wordChunk,List.length_cons,pairBits_length,List.length_replicate,List.length_nil]
    omega
  · simp;omega
lemma candidate_bounds (R : List VertexRecord) (i k m : ℕ) (A : Accum) :
    (runCandidates R k i m A).count≤A.count+m ∧
      (runCandidates R k i m A).lows.length≤A.lows.length+m*(2*R.length+2) ∧
      (runCandidates R k i m A).highs.length≤A.highs.length+m*(2*R.length+2) := by
  induction m generalizing i A with
  | zero => simp [runCandidates]
  | succ m ih =>
    have hs:=step_bounds R i k A
    have hh:=ih (i+1) (step R i k A)
    simp only [runCandidates]
    constructor
    · omega
    constructor <;> nlinarith
lemma rank_bounds (R : List VertexRecord) (k m : ℕ) (A : Accum) :
    (runRanks R k m A).count≤A.count+m*R.length ∧
      (runRanks R k m A).lows.length≤A.lows.length+m*R.length*(2*R.length+2) ∧
      (runRanks R k m A).highs.length≤A.highs.length+m*R.length*(2*R.length+2) := by
  induction m generalizing k A with
  | zero => simp [runRanks]
  | succ m ih =>
    have hs:=candidate_bounds R 0 k R.length A
    have hh:=ih (k+1) (runCandidates R k 0 R.length A)
    simp only [runRanks]
    constructor
    · nlinarith
    constructor <;> nlinarith
lemma result_bounds (R : List VertexRecord) :
    (result R).count≤R.length^2 ∧ (result R).lows.length≤2*R.length^3+2*R.length^2 ∧
      (result R).highs.length≤2*R.length^3+2*R.length^2 := by
  have h:=rank_bounds R 0 R.length initialAccum
  simp only [initialAccum,List.length_nil,Nat.zero_add] at h
  dsimp only [result,initialAccum]
  constructor
  · nlinarith [h.1]
  constructor <;> nlinarith [h.2.1,h.2.2]
noncomputable def timePolynomial : Polynomial ℕ := 100000*(X+1)^6
lemma cost_polynomial (R : List VertexRecord) :
    R.length*(rowBound R.length (encodeBitList (R.map encodeVertex)).length+2)+6*R.length+
        10*(result R).count+12*(result R).lows.length+12*(result R).highs.length+56≤
      timePolynomial.eval (R.length+(encodeBitList (R.map encodeVertex)).length) := by
  let n:=R.length
  let L:=(encodeBitList (R.map encodeVertex)).length
  have hb:=result_bounds R
  have hn:n≤n+L:=by omega
  have hl:L≤n+L:=by omega
  calc
    _≤n*(rowBound n L+2)+6*n+10*n^2+24*(2*n^3+2*n^2)+56:=by dsimp only[n,L];omega
    _≤(n+L)*(rowBound (n+L) (n+L)+2)+6*(n+L)+10*(n+L)^2+24*(2*(n+L)^3+2*(n+L)^2)+56:=by
      unfold rowBound cellBound countBound MonotoneOrderRuntime.bound lookupBound
      gcongr
    _≤timePolynomial.eval (n+L):=by
      simp only [timePolynomial,eval_mul,eval_pow,eval_add,eval_X,eval_ofNat,eval_one]
      unfold rowBound cellBound countBound MonotoneOrderRuntime.bound lookupBound
      ring_nf
      omega
lemma program_computed_polynomial (g : BitString→ℕ) (R : List VertexRecord) :
    ∃c,program.Executes g (initial R) (clean R (computedBits R)) c ∧
      c≤timePolynomial.eval (R.length+(encodeBitList (R.map encodeVertex)).length) := by
  obtain ⟨c,hc,hb⟩:=program_executes g R
  exact ⟨c,hc,hb.trans (cost_polynomial R)⟩
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
