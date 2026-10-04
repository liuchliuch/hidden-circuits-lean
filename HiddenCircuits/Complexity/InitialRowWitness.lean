import HiddenCircuits.Complexity.InitialRowLoops

namespace HiddenCircuits.Complexity.InitialRowEmitter
open OracleBlock TM2BooleanEncoding InitialSourceClassifier
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def witnessBody : OracleBlock 11 := seq (slot M .witness) (push 0 true)
noncomputable def witnessLoop : OracleBlock 11 := whilePop 10 (witnessBody M) (witnessBody M)
noncomputable def witnessBits : ℕ → ℕ → ℕ → BitString
  | _, _, 0 => []
  | source, target, count+1 => InitialRowFamily.symbolBits M .witness source target ++
      witnessBits (source+1) (target+symbolBits M.tm) count

theorem witnessBody_executes (g : BitString → ℕ) (source target : ℕ)
    (x : BitString) (m H remaining witness : ℕ) (stream : BitString) :
    ∃ cost, (witnessBody M).Executes g (state source target x m H [] (remaining+1) witness stream)
      (state (source+1) (target+symbolBits M.tm) x m H [] remaining witness
        ((InitialRowFamily.symbolBits M .witness source target).reverse++stream)) cost ∧
      cost ≤ familyBound source target (symbolBits M.tm)+5 := by
  obtain ⟨c,hc,hb⟩ := slot_executes M g .witness source target x m H [] remaining witness stream
  have hp : (push (0 : Fin 12) true).Executes g
      (state source (target+symbolBits M.tm) x m H [] remaining witness
        ((InitialRowFamily.symbolBits M .witness source target).reverse++stream))
      (state (source+1) (target+symbolBits M.tm) x m H [] remaining witness
        ((InitialRowFamily.symbolBits M .witness source target).reverse++stream)) 1 := by
    convert push_executes g (0 : Fin 12) true
      (state source (target+symbolBits M.tm) x m H [] remaining witness
        ((InitialRowFamily.symbolBits M .witness source target).reverse++stream)) using 1
    funext i;fin_cases i <;> simp [state,List.replicate_succ]
  exact ⟨c+1+2,seq_executes _ _ g hc hp,by omega⟩

lemma pop_witness (source target : ℕ) (x : BitString) (m H remaining witness : ℕ) (stream : BitString) :
    Function.update (state source target x m H [] remaining (witness+1) stream) 10 (List.replicate witness true) =
      state source target x m H [] remaining witness stream := by
  funext i;fin_cases i <;> rfl

theorem witnessLoop_execution (g : BitString → ℕ) (source target : ℕ)
    (x : BitString) (m H count remaining : ℕ) (stream : BitString) :
    ∃ cost, WhileExecution (10 : Fin 12) (witnessBody M) (witnessBody M) g
      (state source target x m H [] (count+remaining) count stream)
      (state (source+count) (target+count*symbolBits M.tm) x m H [] remaining 0
        ((witnessBits M source target count).reverse++stream)) cost ∧
      cost ≤ count*(familyBound (source+count) (target+count*symbolBits M.tm) (symbolBits M.tm)+7)+1 := by
  induction count generalizing source target stream with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [witnessBits] using WhileExecution.empty (state source target x m H [] remaining 0 stream) rfl
  | succ count ih =>
    obtain ⟨cb,hb,hbb⟩ := witnessBody_executes M g source target x m H (count+remaining) count stream
    obtain ⟨ct,ht,hbt⟩ := ih (source+1) (target+symbolBits M.tm)
      ((InitialRowFamily.symbolBits M .witness source target).reverse++stream)
    have hbody : (witnessBody M).Executes g
        (Function.update (state source target x m H [] (count+1+remaining) (count+1) stream) 10 (List.replicate count true))
        (state (source+1) (target+symbolBits M.tm) x m H [] (count+remaining) count
          ((InitialRowFamily.symbolBits M .witness source target).reverse++stream)) cb := by
      rw [pop_witness]
      convert hb using 1 <;> congr 1 <;> omega
    have hs : (state source target x m H [] (count+1+remaining) (count+1) stream) 10 = true::List.replicate count true := rfl
    have hr := WhileExecution.one hs hbody ht
    refine ⟨1+cb+1+ct,?_,?_⟩
    · convert hr using 1 <;> simp [witnessBits,List.reverse_append,List.append_assoc] <;> congr 1 <;> ring
    · have heq : target+symbolBits M.tm+count*symbolBits M.tm=target+(count+1)*symbolBits M.tm := by ring
      rw [heq,show source+1+count=source+(count+1) by omega] at hbt
      have hm := familyBound_mono (symbolBits M.tm) (a:=source) (c:=source+(count+1))
        (b:=target) (d:=target+(count+1)*symbolBits M.tm) (by omega) (by omega)
      nlinarith

theorem witnessLoop_executes (g : BitString → ℕ) (source target : ℕ)
    (x : BitString) (m H count remaining : ℕ) (stream : BitString) :
    ∃ cost, (witnessLoop M).Executes g (state source target x m H [] (count+remaining) count stream)
      (state (source+count) (target+count*symbolBits M.tm) x m H [] remaining 0
        ((witnessBits M source target count).reverse++stream)) cost ∧
      cost ≤ count*(familyBound (source+count) (target+count*symbolBits M.tm) (symbolBits M.tm)+7)+1 := by
  obtain ⟨c,hc,hb⟩ := witnessLoop_execution M g source target x m H count remaining stream
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩

noncomputable def paddingLoop : OracleBlock 11 := whilePop 9 (symbols M .empty) (symbols M .empty)
noncomputable def paddingBits (source : ℕ) : ℕ → ℕ → BitString
  | _, 0 => []
  | target, count+1 => InitialRowFamily.symbolBits M .empty source target ++
      paddingBits source (target+symbolBits M.tm) count

theorem paddingLoop_execution (g : BitString → ℕ) (source target : ℕ)
    (x : BitString) (m H count : ℕ) (stream : BitString) :
    ∃ cost, WhileExecution (9 : Fin 12) (symbols M .empty) (symbols M .empty) g
      (state source target x m H [] count 0 stream)
      (state source (target+count*symbolBits M.tm) x m H [] 0 0
        ((paddingBits M source target count).reverse++stream)) cost ∧
      cost ≤ count*(familyBound source (target+count*symbolBits M.tm) (symbolBits M.tm)+2)+1 := by
  induction count generalizing target stream with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [paddingBits] using WhileExecution.empty (state source target x m H [] 0 0 stream) rfl
  | succ count ih =>
    obtain ⟨cb,hb,hbb⟩ := symbols_executes M g .empty source target x m H [] count 0 stream
    obtain ⟨ct,ht,hbt⟩ := ih (target+symbolBits M.tm)
      ((InitialRowFamily.symbolBits M .empty source target).reverse++stream)
    have hbody : (symbols M .empty).Executes g
        (Function.update (state source target x m H [] (count+1) 0 stream) 9 (List.replicate count true))
        (state source (target+symbolBits M.tm) x m H [] count 0
          ((InitialRowFamily.symbolBits M .empty source target).reverse++stream)) cb := by
      rwa [pop_remaining]
    have hs : (state source target x m H [] (count+1) 0 stream) 9 = true::List.replicate count true := rfl
    have hr := WhileExecution.one hs hbody ht
    refine ⟨1+cb+1+ct,?_,?_⟩
    · convert hr using 1 <;> simp [paddingBits,List.reverse_append,List.append_assoc] <;> congr 1 <;> ring
    · have heq : target+symbolBits M.tm+count*symbolBits M.tm=target+(count+1)*symbolBits M.tm := by ring
      rw [heq] at hbt
      have hm := familyBound_mono (symbolBits M.tm) (a:=source) (c:=source)
        (b:=target) (d:=target+(count+1)*symbolBits M.tm) le_rfl (by omega)
      nlinarith

theorem paddingLoop_executes (g : BitString → ℕ) (source target : ℕ)
    (x : BitString) (m H count : ℕ) (stream : BitString) :
    ∃ cost, (paddingLoop M).Executes g (state source target x m H [] count 0 stream)
      (state source (target+count*symbolBits M.tm) x m H [] 0 0
        ((paddingBits M source target count).reverse++stream)) cost ∧
      cost ≤ count*(familyBound source (target+count*symbolBits M.tm) (symbolBits M.tm)+2)+1 := by
  obtain ⟨c,hc,hb⟩ := paddingLoop_execution M g source target x m H count stream
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩

lemma witnessBody_queryFree : (witnessBody M).QueryFree := seq_queryFree _ _ (slot_queryFree M _) (push_queryFree _ _)
lemma witnessLoop_queryFree : (witnessLoop M).QueryFree := whilePop_queryFree _ _ _ (witnessBody_queryFree M) (witnessBody_queryFree M)
lemma paddingLoop_queryFree : (paddingLoop M).QueryFree := whilePop_queryFree _ _ _ (symbols_queryFree M _) (symbols_queryFree M _)

end HiddenCircuits.Complexity.InitialRowEmitter
