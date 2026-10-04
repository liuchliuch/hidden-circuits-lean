import HiddenCircuits.Circuit.Runtime.SampleLocalWords
import HiddenCircuits.Circuit.Runtime.SampleLocalMetadata

namespace HiddenCircuits.Circuit.Runtime.SampleLocalEmitter
open HiddenCircuits.Complexity OracleBlock

lemma wordBitsAt_lift {n r : ℕ} (p : Placement n r) (w : List (Letter (blockWidth r))) :
    LetterEmitter.wordBitsAt (4*p.before) w=encodeBitList ((p.liftWord w).map letterBits) := by
  rw [←LetterEmitter.chunks_eq]
  simp [LetterEmitter.wordBitsAt,Placement.liftWord,projectedMiddleWord,splitWordLeft,splitWordRight,
    List.flatMap_map,Letter.inLeft,Letter.inRight,leftIndex,rightIndex,blockWidth]

noncomputable def one (a : OneGate) : OracleBlock 8 := seq (fixed (oneGateWord a).word) (oneMetadata a)
noncomputable def sample : OracleBlock 8 := seq sampleWord (addExponent 290 372)

theorem one_executes (g : BitString → ℕ) (a : OneGate) (p u : ℕ) (out exponent : BitString) (negative : Bool) :
    (one a).Executes g (store p u 0 out exponent [negative] [] [] [])
      (store p u 0 ((LetterEmitter.wordBitsAt p (oneGateWord a).word).reverse++out)
        (List.replicate (SampleScalar.oneExponent a) true++exponent) [oneNegative a negative] [] [] [])
      (LetterEmitter.wordCost p (oneGateWord a).word+oneMetadataCost a+2) :=
  seq_executes _ _ g (fixed_executes g _ p u 0 out exponent [negative])
    (oneMetadata_executes g a p u _ exponent negative)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem sample_executes (g : BitString → ℕ) (p u : ℕ) (out exponent sign : BitString) :
    sample.Executes g (store p u 0 out exponent sign [] [] [])
      (store p u 0 ((sampleBits p u).reverse++out)
        (List.replicate (290*u+372) true++exponent) sign [] [] []) (sampleCost p u+878*u+1126) := by
  have h := seq_executes sampleWord (addExponent 290 372) g (sampleWord_executes g p u out exponent sign)
    (addExponent_executes g 290 372 p u ((sampleBits p u).reverse++out) exponent sign)
  have he : sampleCost p u+((3*290+8)*u+3*372+8)+2=sampleCost p u+878*u+1126 := by omega
  rw [he] at h
  exact h

lemma one_cost_bound (a : OneGate) (p : ℕ) :
    LetterEmitter.wordCost p (oneGateWord a).word+oneMetadataCost a+2≤20000*(p+1) := by
  have hw := LetterEmitter.wordCost_bound p (oneGateWord a).word
  have hl := oneGateWord_length a
  have hm : (oneGateWord a).word.length*(14*p+20*4+52)≤88*(14*p+132) :=
    Nat.mul_le_mul_right (14*p+132) hl
  have he : oneMetadataCost a≤81 := by cases a <;> decide +kernel
  change LetterEmitter.wordCost p (oneGateWord a).word≤(oneGateWord a).word.length*(14*p+20*4+52)+1 at hw
  nlinarith

lemma sample_cost_bound (p u : ℕ) : sampleCost p u+878*u+1126≤2000000*(p+u+1)^2 := by
  have h := sampleCost_bound p u
  have hu : u+1≤(p+u+1)^2 := by nlinarith [Nat.zero_le (p*u)]
  omega

lemma one_queryFree (a : OneGate) : (one a).QueryFree := seq_queryFree _ _ (fixed_queryFree _) (oneMetadata_queryFree a)
lemma sample_queryFree : sample.QueryFree := seq_queryFree _ _ sampleWord_queryFree (addExponent_queryFree _ _)

/-- The actual local one-bit word, at the exact physical offset dictated by its placement. -/
theorem placedOne_executes {n : ℕ} (g : BitString → ℕ) (a : OneGate) (p : Placement n 1) (u : ℕ)
    (out exponent : BitString) (negative : Bool) :
    ∃ cost, (one a).Executes g (store (4*p.before) u 0 out exponent [negative] [] [] [])
      (store (4*p.before) u 0 ((encodeBitList ((placedOneGateWord p a).word.map letterBits)).reverse++out)
        (List.replicate (SampleScalar.oneExponent a) true++exponent) [oneNegative a negative] [] [] []) cost ∧
      cost≤20000*(4*p.before+1) := by
  refine ⟨_,?_,one_cost_bound a (4*p.before)⟩
  simpa only [wordBitsAt_lift,placedOneGateWord,ScaledWord.lift] using one_executes g a (4*p.before) u out exponent negative

/-- The shared sample loop emits the actual placed physical G word, not an assumed word primitive. -/
theorem placedSample_executes {n : ℕ} (g : BitString → ℕ) (p : Placement n 2) (u : ℕ)
    (out exponent sign : BitString) :
    ∃ cost, sample.Executes g (store (4*p.before) u 0 out exponent sign [] [] [])
      (store (4*p.before) u 0 ((encodeBitList (((sampleGWord u).lift p).word.map letterBits)).reverse++out)
        (List.replicate (290*u+372) true++exponent) sign [] [] []) cost ∧
      cost≤2000000*(4*p.before+u+1)^2 := by
  refine ⟨_,?_,sample_cost_bound (4*p.before) u⟩
  simpa only [sampleBits_eq,wordBitsAt_lift,ScaledWord.lift] using sample_executes g (4*p.before) u out exponent sign

end HiddenCircuits.Circuit.Runtime.SampleLocalEmitter
