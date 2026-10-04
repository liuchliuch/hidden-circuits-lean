import HiddenCircuits.Circuit.Runtime.SourceSampleFrame

/-! Actual finite integer factor multiplication, online
rational accumulation, and cleanup for a source-grid sample. -/
namespace HiddenCircuits.Circuit.Runtime.SourceSample
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial
open RegisterMachine

def numeratorRegisters (a b c d e : ℤ) : Fin 7→ℤ := ![a,b,c,d,e,0,0]
def numeratorCode : List Instruction := [⟨.multiply,0,0,1⟩,⟨.multiply,0,0,2⟩,⟨.multiply,0,0,3⟩,⟨.multiply,0,0,4⟩]
def denominatorRegisters (a b c d : ℤ) : Fin 7→ℤ := ![a,b,c,d,0,0,0]
def denominatorCode : List Instruction := [⟨.multiply,0,0,1⟩,⟨.multiply,0,0,2⟩,⟨.multiply,0,0,3⟩]
noncomputable def numeratorProduct : OracleBlock 63 := rename (compile numeratorCode) numeratorEmbedding
noncomputable def denominatorProduct : OracleBlock 63 := rename (compile denominatorCode) denominatorEmbedding
noncomputable def numeratorTime : Polynomial ℕ := straightTime numeratorCode
noncomputable def denominatorTime : Polynomial ℕ := straightTime denominatorCode
noncomputable def copyDenominator : OracleBlock 63 := copyOn 9 22 24 (by decide) (by decide) (by decide)
noncomputable def accumulate : OracleBlock 63 := RationalAccumulator.on accumulatorEmbedding
noncomputable def clearSample : OracleBlock 63 := clearList [14,15,16,17,18,19,21,31]

lemma numerator_evaluate (a b c d e : ℤ) : evaluate numeratorCode (numeratorRegisters a b c d e)=numeratorRegisters (a*b*c*d*e) b c d e := by
  funext i;fin_cases i <;> simp [evaluate,numeratorCode,numeratorRegisters,Instruction.eval,Operation.eval]
lemma denominator_evaluate (a b c d : ℤ) : evaluate denominatorCode (denominatorRegisters a b c d)=denominatorRegisters (a*b*c*d) b c d := by
  funext i;fin_cases i <;> simp [evaluate,denominatorCode,denominatorRegisters,Instruction.eval,Operation.eval]

set_option maxHeartbeats 1000000 in
lemma numeratorProduct_executes (g : BitString → ℕ) (p : Parameters) (v : Values) (a b c d e : ℤ) (B : ℕ)
    (ha : v.firstNumerator=signedBits a) (hb : v.secondNumerator=signedBits b)
    (hc : v.geometricNumerator=signedBits c) (hd : v.dyadicNumerator=signedBits d) (he : v.answer=signedBits e)
    (hB : ∀i,(SourceSample.store p v i).length≤B) :
    ∃t,numeratorProduct.Executes g (SourceSample.store p v)
      (SourceSample.store p {v with firstNumerator:=signedBits (a*b*c*d*e)}) t ∧ t≤numeratorTime.eval B := by
  have hR : RegisterMachine.Bounded B (numeratorRegisters a b c d e) := by
    intro i;fin_cases i
    · simpa [numeratorRegisters,SourceSample.store,ha] using hB 20
    · simpa [numeratorRegisters,SourceSample.store,hb] using hB 21
    · simpa [numeratorRegisters,SourceSample.store,hc] using hB 14
    · simpa [numeratorRegisters,SourceSample.store,hd] using hB 19
    · simpa [numeratorRegisters,SourceSample.store,he] using hB 31
    · exact hB 55
    · exact hB 56
  obtain ⟨t,ht,htb⟩:=compile_polynomial numeratorCode g (numeratorRegisters a b c d e) B hR
    (by simp [numeratorCode,Valid,Operation.Valid])
  rw [numerator_evaluate] at ht
  refine ⟨t,?_,htb⟩
  apply rename_executes_to _ numeratorEmbedding g ht
  · funext i;fin_cases i <;> simp [numeratorEmbedding,SourceSample.store,RegisterMachine.store,numeratorRegisters,ha,hb,hc,hd,he,Function.comp_def]
  · funext i;fin_cases i <;> simp [numeratorEmbedding,SourceSample.store,RegisterMachine.store,numeratorRegisters,hb,hc,hd,he,Function.comp_def]
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 9 rfl).elim

set_option maxHeartbeats 1000000 in
lemma denominatorProduct_executes (g : BitString → ℕ) (p : Parameters) (v : Values) (a b c d : ℤ) (B : ℕ)
    (ha : v.itemDenominator=signedBits a) (hb : p.secondDenominator=signedBits b)
    (hc : v.geometricDenominator=signedBits c) (hd : v.dyadicDenominator=signedBits d)
    (hB : ∀i,(SourceSample.store p v i).length≤B) :
    ∃t,denominatorProduct.Executes g (SourceSample.store p v)
      (SourceSample.store p {v with itemDenominator:=signedBits (a*b*c*d)}) t ∧ t≤denominatorTime.eval B := by
  have hR : RegisterMachine.Bounded B (denominatorRegisters a b c d) := by
    intro i;fin_cases i
    · simpa [denominatorRegisters,SourceSample.store,ha] using hB 22
    · simpa [denominatorRegisters,SourceSample.store,hb] using hB 10
    · simpa [denominatorRegisters,SourceSample.store,hc] using hB 15
    · simpa [denominatorRegisters,SourceSample.store,hd] using hB 18
    · exact hB 55
    · exact hB 56
    · exact hB 57
  obtain ⟨t,ht,htb⟩:=compile_polynomial denominatorCode g (denominatorRegisters a b c d) B hR
    (by simp [denominatorCode,Valid,Operation.Valid])
  rw [denominator_evaluate] at ht
  refine ⟨t,?_,htb⟩
  apply rename_executes_to _ denominatorEmbedding g ht
  · funext i;fin_cases i <;> simp [denominatorEmbedding,SourceSample.store,RegisterMachine.store,denominatorRegisters,ha,hb,hc,hd,Function.comp_def]
  · funext i;fin_cases i <;> simp [denominatorEmbedding,SourceSample.store,RegisterMachine.store,denominatorRegisters,hb,hc,hd,Function.comp_def]
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 9 rfl).elim

lemma copyDenominator_executes (g : BitString → ℕ) (p : Parameters) (v : Values) (hv : v.itemDenominator=[]) :
    copyDenominator.Executes g (SourceSample.store p v) (SourceSample.store p {v with itemDenominator:=p.firstDenominator}) (5*p.firstDenominator.length+2) := by
  have h:=copyOn_executes g (9:Fin 64) 22 24 (by decide) (by decide) (by decide) (SourceSample.store p v) rfl
  change copyDenominator.Executes g (SourceSample.store p v)
    (Function.update (SourceSample.store p v) (22:Fin 64) (p.firstDenominator++v.itemDenominator)) (5*p.firstDenominator.length+2) at h
  simpa only [hv,List.append_nil,update_itemDenominator] using h

set_option maxHeartbeats 1000000 in
lemma accumulate_executes (g : BitString → ℕ) (p : Parameters) (v : Values) (item : ℤ×ℤ) (B : ℕ)
    (hn : v.firstNumerator=signedBits item.1) (hd : v.itemDenominator=signedBits item.2)
    (hB : ∀i,(SourceSample.store p v i).length≤B) :
    ∃t,accumulate.Executes g (SourceSample.store p v)
      (SourceSample.store p {v with accumulator:=RationalAccumulator.step v.accumulator item,firstNumerator:=[],itemDenominator:=[]}) t ∧
      t≤RationalAccumulator.time.eval B := by
  apply RationalAccumulator.on_executes_to accumulatorEmbedding g _ _ v.accumulator item B
  · funext i;fin_cases i <;> simp [accumulatorEmbedding,SourceSample.store,RationalAccumulator.input,hn,hd,Function.comp_def]
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 9 rfl).elim | exact (hi 10 rfl).elim | exact (hi 11 rfl).elim | exact (hi 12 rfl).elim
  · exact ⟨hB 11,hB 12⟩
  · constructor
    · simpa [SourceSample.store,hn] using hB 20
    · simpa [SourceSample.store,hd] using hB 22

set_option maxHeartbeats 1000000 in
lemma clearSample_executes (g : BitString → ℕ) (p : Parameters) (v : Values) (B : ℕ)
    (hn : v.firstNumerator=[]) (hd : v.itemDenominator=[]) (hq : v.query=[])
    (hB : ∀i,(SourceSample.store p v i).length≤B) :
    ∃t,clearSample.Executes g (SourceSample.store p v)
      (SourceSample.store p {accumulator:=v.accumulator,degree:=v.degree}) t ∧ t≤8*(B+3)+1 := by
  obtain ⟨t,ht,hb⟩:=clearList_executes g ([14,15,16,17,18,19,21,31]:List (Fin 64)) (SourceSample.store p v) B hB
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext i;fin_cases i <;> simp [eraseStore,SourceSample.store,hn,hd,hq]
end HiddenCircuits.Circuit.Runtime.SourceSample
