import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerializeCell
import HiddenCircuits.GraphReduction.UnitIntervalGraphInput

/-! The loop reads every actual unary coordinate, emits its signed binary word,
and returns all temporary stacks empty. Bounds depend only on length and values. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def unaryWords (xs : List ℕ) : List BitString := xs.map (fun a=>List.replicate a true)
def binaryWords (xs : List ℕ) : List BitString := xs.map (fun (a : ℕ)=>signedBits (a:ℤ))
def nativeBytes (D : ℕ) (xs : List ℕ) : BitString := encodeBitList (signedBits (D:ℤ)::binaryWords xs)
noncomputable def loop : OracleBlock 8 := whilePop 3 skip body

lemma loop_executes (g : BitString → ℕ) (values : BitString) (D : ℕ) (xs : List ℕ)
    (acc : BitString) (B : ℕ) (hx : ∀a∈xs,a≤B) :
    ∃t,loop.Executes g (coreState values D [] (encodeBitList (unaryWords xs)) [] [] acc)
      (coreState values D [] [] [] [] ((encodeBitList (binaryWords xs)).reverse++acc)) t ∧
      t≤xs.length*(cellBound B+2)+1 := by
  suffices ∃t,WhileExecution (3:Fin 9) skip body g
      (coreState values D [] (encodeBitList (unaryWords xs)) [] [] acc)
      (coreState values D [] [] [] [] ((encodeBitList (binaryWords xs)).reverse++acc)) t ∧
      t≤xs.length*(cellBound B+2)+1 by
    obtain ⟨t,ht,hb⟩:=this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction xs generalizing acc with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [unaryWords,binaryWords,encodeBitList] using
      (WhileExecution.empty (stack:=(3:Fin 9)) (B:=skip) (C:=body) (g:=g)
        (coreState values D [] [] [] [] acc) rfl)
  | cons a xs ih =>
    obtain ⟨t,ht,hb⟩:=body_executes g values D a (encodeBitList (unaryWords xs)) acc
    obtain ⟨c,hc,hcb⟩:=ih ((wordChunk (signedBits (a:ℤ))).reverse++acc)
      (fun a ha=>hx a (by simp [ha]))
    have he : Function.update (coreState values D [] (encodeBitList (unaryWords (a::xs))) [] [] acc)
        (3:Fin 9) (pairBits (List.replicate a true) (encodeBitList (unaryWords xs)))=
        coreState values D [] (pairBits (List.replicate a true) (encodeBitList (unaryWords xs))) [] [] acc := by
      funext i;fin_cases i <;> rfl
    rw [←he] at ht
    have hh:=WhileExecution.one
      (show coreState values D [] (encodeBitList (unaryWords (a::xs))) [] [] acc 3=
        true::pairBits (List.replicate a true) (encodeBitList (unaryWords xs)) from rfl) ht hc
    refine ⟨1+t+1+c,?_,?_⟩
    · simpa [binaryWords,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc] using hh
    · have hm:=cellBound_mono (hx a (by simp))
      simp only [List.length_cons]
      nlinarith

lemma unary_stream_length (xs : List ℕ) (B : ℕ) (hx : ∀a∈xs,a≤B) :
    (encodeBitList (unaryWords xs)).length≤xs.length*(2*B+2) := by
  have h:=UnitIntervalGraphInput.encode_list_bound (unaryWords xs) B (by
    intro w hw;obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hw
    simpa using hx a ha)
  simpa [unaryWords] using h

lemma native_length (D : ℕ) (xs : List ℕ) (B : ℕ) (hx : ∀a∈xs,a≤B) :
    (nativeBytes D xs).length≤(2*D+4)+xs.length*(2*B+4) := by
  have h:=UnitIntervalGraphInput.encode_list_bound (binaryWords xs) (B+1) (by
    intro w hw;obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hw
    exact (signed_length a).trans (Nat.add_le_add_right (hx a ha) 1))
  have hd:=signed_length D
  have hc:(wordChunk (signedBits (D:ℤ))).length=2*(signedBits (D:ℤ)).length+2 := by
    simp [wordChunk,pairBits_length]
  have he:nativeBytes D xs=wordChunk (signedBits (D:ℤ))++encodeBitList (binaryWords xs) := by
    simp [nativeBytes,encodeBitList_eq_chunks]
  rw [he,List.length_append,hc]
  simpa only [binaryWords,List.length_map,show 2*(B+1)+2=2*B+4 by omega] using Nat.add_le_add (by omega : 2*(signedBits (D:ℤ)).length+2≤2*D+4) h

lemma loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ skip_queryFree body_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
