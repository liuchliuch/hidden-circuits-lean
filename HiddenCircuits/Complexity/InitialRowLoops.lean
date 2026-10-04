import HiddenCircuits.Complexity.InitialRowEmitter

namespace HiddenCircuits.Complexity.InitialRowEmitter
open OracleBlock TM2BooleanEncoding InitialSourceClassifier
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def prefixBody (b : Bool) : OracleBlock 11 := seq (slot M (.value true)) (slot M (.value b))
noncomputable def prefixLoop : OracleBlock 11 := whilePop 8 (prefixBody M false) (prefixBody M true)
noncomputable def prefixBits (source : ℕ) : ℕ → BitString → BitString
  | _, [] => []
  | target, b::bs => InitialRowFamily.symbolBits M (.value true) source target ++
      InitialRowFamily.symbolBits M (.value b) source (target+symbolBits M.tm) ++
      prefixBits source (target+2*symbolBits M.tm) bs

theorem prefixBody_executes (g : BitString → ℕ) (b : Bool) (source target : ℕ)
    (x : BitString) (m H : ℕ) (input : BitString) (remaining witness : ℕ) (stream : BitString) :
    ∃ cost, (prefixBody M b).Executes g (state source target x m H input (remaining+2) witness stream)
      (state source (target+2*symbolBits M.tm) x m H input remaining witness
        ((InitialRowFamily.symbolBits M (.value b) source (target+symbolBits M.tm)).reverse++
          (InitialRowFamily.symbolBits M (.value true) source target).reverse++stream)) cost ∧
      cost ≤ 2*familyBound source (target+2*symbolBits M.tm) (symbolBits M.tm)+6 := by
  obtain ⟨c1,h1,hb1⟩ := slot_executes M g (.value true) source target x m H input (remaining+1) witness stream
  obtain ⟨c2,h2,hb2⟩ := slot_executes M g (.value b) source (target+symbolBits M.tm) x m H input remaining witness
    ((InitialRowFamily.symbolBits M (.value true) source target).reverse++stream)
  refine ⟨c1+c2+2,?_,?_⟩
  · convert seq_executes _ _ g h1 h2 using 1 <;> simp [List.append_assoc] <;> congr 1 <;> omega
  · have h1m := familyBound_mono (symbolBits M.tm) (a:=source) (c:=source) (b:=target)
      (d:=target+2*symbolBits M.tm) le_rfl (by omega)
    have h2m := familyBound_mono (symbolBits M.tm) (a:=source) (c:=source) (b:=target+symbolBits M.tm)
      (d:=target+2*symbolBits M.tm) le_rfl (by omega)
    omega

lemma pop_input (source target : ℕ) (x : BitString) (m H : ℕ) (b : Bool)
    (input : BitString) (remaining witness : ℕ) (stream : BitString) :
    Function.update (state source target x m H (b::input) remaining witness stream) 8 input =
      state source target x m H input remaining witness stream := by
  funext i;fin_cases i <;> rfl

theorem prefixLoop_execution (g : BitString → ℕ) (source target : ℕ)
    (x : BitString) (m H : ℕ) (input : BitString) (remaining witness : ℕ) (stream : BitString) :
    ∃ cost, WhileExecution (8 : Fin 12) (prefixBody M false) (prefixBody M true) g
      (state source target x m H input (2*input.length+remaining) witness stream)
      (state source (target+2*input.length*symbolBits M.tm) x m H [] remaining witness
        ((prefixBits M source target input).reverse++stream)) cost ∧
      cost ≤ input.length*(2*familyBound source (target+2*input.length*symbolBits M.tm) (symbolBits M.tm)+8)+1 := by
  induction input generalizing target stream with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [prefixBits] using WhileExecution.empty (state source target x m H [] remaining witness stream) rfl
  | cons b bs ih =>
    obtain ⟨cb,hb,hbb⟩ := prefixBody_executes M g b source target x m H bs (2*bs.length+remaining) witness stream
    let acc := (InitialRowFamily.symbolBits M (.value b) source (target+symbolBits M.tm)).reverse++
      (InitialRowFamily.symbolBits M (.value true) source target).reverse++stream
    obtain ⟨ct,ht,hbt⟩ := ih (target+2*symbolBits M.tm) acc
    have hbody : (prefixBody M b).Executes g
        (Function.update (state source target x m H (b::bs) (2*(b::bs).length+remaining) witness stream) 8 bs)
        (state source (target+2*symbolBits M.tm) x m H bs (2*bs.length+remaining) witness acc) cb := by
      rw [pop_input]
      convert hb using 1 <;> simp only [List.length_cons] <;> congr 1 <;> omega
    have he : (state source target x m H (b::bs) (2*(b::bs).length+remaining) witness stream) 8 = b::bs := rfl
    have hr : WhileExecution (8 : Fin 12) (prefixBody M false) (prefixBody M true) g
        (state source target x m H (b::bs) (2*(b::bs).length+remaining) witness stream)
        (state source (target+2*symbolBits M.tm+2*bs.length*symbolBits M.tm) x m H [] remaining witness
          ((prefixBits M source (target+2*symbolBits M.tm) bs).reverse++acc)) (1+cb+1+ct) := by
      cases b
      · exact WhileExecution.zero he hbody ht
      · exact WhileExecution.one he hbody ht
    refine ⟨1+cb+1+ct,?_,?_⟩
    · convert hr using 1 <;> simp [prefixBits,acc,List.reverse_append,List.append_assoc] <;> congr 1 <;> ring
    · have heq : target+2*symbolBits M.tm+2*bs.length*symbolBits M.tm = target+2*(bs.length+1)*symbolBits M.tm := by ring
      rw [heq] at hbt
      have hm := familyBound_mono (symbolBits M.tm) (a:=source) (c:=source)
        (b:=target+2*symbolBits M.tm) (d:=target+2*(bs.length+1)*symbolBits M.tm) le_rfl (by nlinarith)
      simp only [List.length_cons]
      nlinarith

theorem prefixLoop_executes (g : BitString → ℕ) (source target : ℕ)
    (x : BitString) (m H : ℕ) (input : BitString) (remaining witness : ℕ) (stream : BitString) :
    ∃ cost, (prefixLoop M).Executes g
      (state source target x m H input (2*input.length+remaining) witness stream)
      (state source (target+2*input.length*symbolBits M.tm) x m H [] remaining witness
        ((prefixBits M source target input).reverse++stream)) cost ∧
      cost ≤ input.length*(2*familyBound source (target+2*input.length*symbolBits M.tm) (symbolBits M.tm)+8)+1 := by
  obtain ⟨c,hc,hb⟩ := prefixLoop_execution M g source target x m H input remaining witness stream
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩

lemma prefixBody_queryFree (b : Bool) : (prefixBody M b).QueryFree :=
  seq_queryFree _ _ (slot_queryFree M _) (slot_queryFree M _)
lemma prefixLoop_queryFree : (prefixLoop M).QueryFree :=
  whilePop_queryFree _ _ _ (prefixBody_queryFree M _) (prefixBody_queryFree M _)

end HiddenCircuits.Complexity.InitialRowEmitter
