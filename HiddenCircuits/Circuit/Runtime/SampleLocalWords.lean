import HiddenCircuits.Circuit.Runtime.SampleLocalLoops

/-! The nine fixed segments of the actual shared geometric sample, including
its literal two-bit projection word after every available gate. -/
namespace HiddenCircuits.Circuit.Runtime.SampleLocalEmitter
open HiddenCircuits.Complexity OracleBlock

abbrev Segment := Bool × AvailableGate 2

def segments : List Segment :=
  [(true,.one firstBit .scale),(true,.one secondBit .scale),
   (false,.interaction fullTwoBits),(false,.one firstBit .swap),
   (true,.one firstBit .scale),(false,.one firstBit .swap),
   (false,.one secondBit .swap),(true,.one secondBit .scale),
   (false,.one secondBit .swap)]

def unitWord (a : AvailableGate 2) : List (Letter 8) :=
  a.compile.word++globalProjectionWord 2

def segmentBits (p u : ℕ) (a : Segment) : BitString :=
  if a.1 then repeatedBits p u (unitWord a.2) else LetterEmitter.wordBitsAt p (unitWord a.2)
def segmentCost (p u : ℕ) (a : Segment) : ℕ :=
  if a.1 then u*(LetterEmitter.wordCost p (unitWord a.2)+7)+5 else LetterEmitter.wordCost p (unitWord a.2)
noncomputable def segmentBlock (a : Segment) : OracleBlock 8 :=
  if a.1 then repeatSample (unitWord a.2) else fixed (unitWord a.2)
noncomputable def sampleWord : OracleBlock 8 := sequence (segments.map segmentBlock)
def sampleBits (p u : ℕ) : BitString := segments.flatMap (segmentBits p u)
def sampleCost (p u : ℕ) : ℕ := (segments.map (segmentCost p u)).sum+19

theorem segment_executes (g : BitString → ℕ) (a : Segment) (p u : ℕ) (out exponent sign : BitString) :
    (segmentBlock a).Executes g (store p u 0 out exponent sign [] [] [])
      (store p u 0 ((segmentBits p u a).reverse++out) exponent sign [] [] []) (segmentCost p u a) := by
  rcases a with ⟨b,a⟩
  cases b
  · exact fixed_executes g (unitWord a) p u 0 out exponent sign
  · exact repeatSample_executes g (unitWord a) p u out exponent sign

theorem sampleWord_executes (g : BitString → ℕ) (p u : ℕ) (out exponent sign : BitString) :
    sampleWord.Executes g (store p u 0 out exponent sign [] [] [])
      (store p u 0 ((sampleBits p u).reverse++out) exponent sign [] [] []) (sampleCost p u) := by
  have h (a : Segment) (_ : a∈segments) (out : BitString) := segment_executes g a p u out exponent sign
  simpa only [update_stream,show segments.length=9 by rfl] using sequence_emit g segments segmentBlock
    (segmentBits p u) (segmentCost p u) (store p u 0 [] exponent sign [] [] []) 2
    (fun a ha out => by simpa only [update_stream] using h a ha out) out

lemma segment_queryFree (a : Segment) : (segmentBlock a).QueryFree := by
  rcases a with ⟨b,a⟩;cases b
  · exact fixed_queryFree _
  · exact repeatSample_queryFree _
lemma sampleWord_queryFree : sampleWord.QueryFree := by
  apply sequence_queryFree
  intro B hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  exact segment_queryFree a

lemma compileProjected_word {k : ℕ} (w : List (ScaledWord k)) :
    (compileProjected w).word=w.flatMap (fun a => a.word++globalProjectionWord k) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [compileProjected,ScaledWord.compose,ih]

def segmentCircuit (u : ℕ) (a : Segment) : List (AvailableGate 2) :=
  if a.1 then List.replicate u a.2 else [a.2]

lemma circuit_eq_segments (u : ℕ) : sampleLocalCircuit u=segments.flatMap (segmentCircuit u) := by
  simp [sampleLocalCircuit,segments,segmentCircuit,List.append_assoc]

lemma sampleBits_eq (p u : ℕ) :
    sampleBits p u=LetterEmitter.wordBitsAt p (sampleGWord u).word := by
  have h (a : Segment) : segmentBits p u a=
      LetterEmitter.wordBitsAt p ((segmentCircuit u a).flatMap unitWord) := by
    rcases a with ⟨b,a⟩
    cases b
    · simp [segmentBits,segmentCircuit,LetterEmitter.wordBitsAt]
    · simp only [segmentBits,segmentCircuit,Bool.true_eq,if_true,List.flatMap_replicate]
      exact (wordBitsAt_repeat p u (unitWord a)).symm
  simp only [sampleBits,sampleGWord,ScaledWord.rescale,compileProjected_word,List.flatMap_map,
    Function.comp_def,circuit_eq_segments,List.flatMap_assoc]
  rw [show segmentBits p u=(fun a => LetterEmitter.wordBitsAt p ((segmentCircuit u a).flatMap unitWord)) from funext h]
  simp [unitWord,LetterEmitter.wordBitsAt,List.flatMap_assoc]
  rfl

lemma unitWord_length (a : AvailableGate 2) : (unitWord a).length≤328 := by
  have ha := a.compile_length
  have hp : (globalProjectionWord 2).length=240 := by decide +kernel
  simp only [unitWord,List.length_append,hp]
  omega

lemma segmentCost_bound (p u : ℕ) (a : Segment) :
    segmentCost p u a≤(u+1)*(328*(14*p+212)+8)+5 := by
  have hc := LetterEmitter.wordCost_bound p (unitWord a.2)
  have hl := unitWord_length a.2
  have hm : (unitWord a.2).length*(14*p+20*8+52)≤328*(14*p+212) :=
    Nat.mul_le_mul_right (14*p+212) hl
  have hcost : LetterEmitter.wordCost p (unitWord a.2)≤328*(14*p+212)+1 := by omega
  rcases a with ⟨b,a⟩
  cases b <;> dsimp [segmentCost]
  · nlinarith
  · nlinarith

lemma sampleCost_bound (p u : ℕ) : sampleCost p u≤1000000*(p+u+1)^2 := by
  have hs : (segments.map (segmentCost p u)).sum≤segments.length*((u+1)*(328*(14*p+212)+8)+5) := by
    simpa only [List.length_map,smul_eq_mul] using List.sum_le_card_nsmul (segments.map (segmentCost p u)) ((u+1)*(328*(14*p+212)+8)+5) (fun a ha => by
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact segmentCost_bound p u b)
  have hl : segments.length=9 := rfl
  rw [hl] at hs
  dsimp [sampleCost]
  nlinarith

end HiddenCircuits.Circuit.Runtime.SampleLocalEmitter
