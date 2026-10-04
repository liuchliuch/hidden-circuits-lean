import HiddenCircuits.Circuit.Runtime.SampleEmitterFrame

namespace HiddenCircuits.Circuit.Runtime.SampleEmitter
open HiddenCircuits.Complexity OracleBlock

lemma prepend_exponents (a b : ℕ) (xs : BitString) :
    List.replicate a true++(List.replicate b true++xs)=List.replicate (b+a) true++xs := by
  rw [←List.append_assoc,←List.replicate_add,Nat.add_comm]

def deltaBytes {n : ℕ} (w : ScaledWord n) : BitString :=
  encodeBitList ((w.word++globalProjectionWord n).map letterBits)
noncomputable def deltaTime (n u : ℕ) : ℕ := 2000000*(4*n+u+1)^2+ProjectionStream.time.eval n+2

theorem oneDelta_executes (g : BitString → ℕ) {n : ℕ} (p : Placement n 1) (a : OneGate)
    (circuit : BitString) (r s u clock : ℕ) (gates atom tag out exponent : BitString) (negative : Bool) :
    ∃cost, (oneDelta a).Executes g (store circuit r s u n (4*p.before) clock gates atom tag out exponent [negative])
      (store circuit r s u n (4*p.before) clock gates atom tag ((deltaBytes (placedOneGateWord p a)).reverse++out)
        (List.replicate (SampleScalar.oneExponent a+SampleScalar.projectionExponent n) true++exponent)
        [SampleLocalEmitter.oneNegative a negative]) cost ∧ cost≤deltaTime n u := by
  have hl := localOne_executes g a circuit r s u n (4*p.before) clock gates atom tag out exponent negative
  obtain ⟨cp,hp,hbp⟩ := projection_executes g circuit r s u n (4*p.before) clock gates atom tag
    ((LetterEmitter.wordBitsAt (4*p.before) (oneGateWord a).word).reverse++out)
    (List.replicate (SampleScalar.oneExponent a) true++exponent) [SampleLocalEmitter.oneNegative a negative]
  refine ⟨LetterEmitter.wordCost (4*p.before) (oneGateWord a).word+SampleLocalEmitter.oneMetadataCost a+2+cp+2,?_,?_⟩
  · have h := seq_executes (localOne a) projection g hl hp
    simpa only [SampleLocalEmitter.wordBitsAt_lift,placedOneGateWord,ScaledWord.lift,deltaBytes,List.map_append,
      BinaryArithmetic.encodeBitList_append,List.reverse_append,prepend_exponents,List.append_assoc] using h
  · have hb := SampleLocalEmitter.one_cost_bound a (4*p.before)
    have hpn : p.before≤n := by have h:=p.size;omega
    have hu : 4*p.before+1≤(4*n+u+1)^2 := by nlinarith [Nat.zero_le (n*u)]
    unfold deltaTime
    omega

theorem sampleDelta_executes (g : BitString → ℕ) {n : ℕ} (p : Placement n 2)
    (circuit : BitString) (r s u clock : ℕ) (gates atom tag out exponent sign : BitString) :
    ∃cost, sampleDelta.Executes g (store circuit r s u n (4*p.before) clock gates atom tag out exponent sign)
      (store circuit r s u n (4*p.before) clock gates atom tag ((deltaBytes ((sampleGWord u).lift p)).reverse++out)
        (List.replicate (290*u+372+SampleScalar.projectionExponent n) true++exponent) sign) cost ∧ cost≤deltaTime n u := by
  have hl := localSample_executes g circuit r s u n (4*p.before) clock gates atom tag out exponent sign
  obtain ⟨cp,hp,hbp⟩ := projection_executes g circuit r s u n (4*p.before) clock gates atom tag
    ((SampleLocalEmitter.sampleBits (4*p.before) u).reverse++out) (List.replicate (290*u+372) true++exponent) sign
  refine ⟨SampleLocalEmitter.sampleCost (4*p.before) u+878*u+1126+cp+2,?_,?_⟩
  · have h := seq_executes localSample projection g hl hp
    simpa only [SampleLocalEmitter.sampleBits_eq,SampleLocalEmitter.wordBitsAt_lift,ScaledWord.lift,deltaBytes,
      List.map_append,BinaryArithmetic.encodeBitList_append,List.reverse_append,prepend_exponents,List.append_assoc] using h
  · have hb := SampleLocalEmitter.sample_cost_bound (4*p.before) u
    have hpn : p.before≤n := by have h:=p.size;omega
    have hpow := Nat.pow_le_pow_left (show 4*p.before+u+1≤4*n+u+1 by omega) 2
    unfold deltaTime
    omega

noncomputable def repeatedSample : OracleBlock 31 := whilePop 13 sampleDelta sampleDelta

lemma pop_clock (circuit : BitString) (r s u n base clock : ℕ) (gates atom tag out exponent sign : BitString) :
    Function.update (store circuit r s u n base (clock+1) gates atom tag out exponent sign) 13 (List.replicate clock true)=
      store circuit r s u n base clock gates atom tag out exponent sign := by
  funext i;fin_cases i <;> rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem repeatedSample_execution (g : BitString → ℕ) {n : ℕ} (p : Placement n 2)
    (circuit : BitString) (r s u count : ℕ) (gates atom tag out exponent sign : BitString) :
    ∃cost, WhileExecution (13:Fin 32) sampleDelta sampleDelta g
      (store circuit r s u n (4*p.before) count gates atom tag out exponent sign)
      (store circuit r s u n (4*p.before) 0 gates atom tag
        (((List.replicate count (deltaBytes ((sampleGWord u).lift p))).flatten).reverse++out)
        (List.replicate (count*(290*u+372+SampleScalar.projectionExponent n)) true++exponent) sign) cost ∧
      cost≤count*(deltaTime n u+2)+1 := by
  induction count generalizing out exponent with
  | zero => exact ⟨1,by simpa using WhileExecution.empty (store circuit r s u n (4*p.before) 0 gates atom tag out exponent sign) rfl,by simp⟩
  | succ count ih =>
    obtain ⟨cb,hb,hbb⟩ := sampleDelta_executes g p circuit r s u count gates atom tag out exponent sign
    obtain ⟨ct,ht,hbt⟩ := ih ((deltaBytes ((sampleGWord u).lift p)).reverse++out)
      (List.replicate (290*u+372+SampleScalar.projectionExponent n) true++exponent)
    rw [←pop_clock circuit r s u n (4*p.before) count gates atom tag out exponent sign] at hb
    have h := WhileExecution.one (stack:=(13:Fin 32)) (B:=sampleDelta) (C:=sampleDelta) (g:=g) rfl hb ht
    refine ⟨1+cb+1+ct,?_,?_⟩
    · convert h using 1
      simp only [List.replicate_succ,List.flatten_cons,List.reverse_append,←List.append_assoc,←List.replicate_add,Nat.add_mul,Nat.one_mul]
    · nlinarith

lemma repeatedSample_queryFree : repeatedSample.QueryFree := whilePop_queryFree _ _ _ sampleDelta_queryFree sampleDelta_queryFree

end HiddenCircuits.Circuit.Runtime.SampleEmitter
