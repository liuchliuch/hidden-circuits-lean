import HiddenCircuits.GraphReduction.Runtime.DescriptorAtom

/-! A literal mask scan emits precisely the selected structural records. Track
indices advance for both mask bits, and the track work stack is cleared. -/
namespace HiddenCircuits.GraphReduction.Runtime.DescriptorMaskRow
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

def records (v : VertexRecord) : BitString → List VertexRecord
  | [] => []
  | b::bs => (if b then [v] else []) ++ records {v with track:=v.track+1} bs

def state (v : VertexRecord) (mask out : BitString) (count : ℕ) : Store 8 := fun i =>
  if h:i.val<8 then DescriptorAtom.state v out count ⟨i.val,h⟩ else mask

def atomEmbedding : Fin 8 ↪ Fin 9 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 9 => z.val) h)
noncomputable def atom : OracleBlock 8 := rename DescriptorAtom.program atomEmbedding
noncomputable def advance : OracleBlock 8 := push 2 true
noncomputable def selected : OracleBlock 8 := seq atom advance
noncomputable def loop : OracleBlock 8 := whilePop 8 advance selected
noncomputable def program : OracleBlock 8 := seq loop (clear 2)

lemma atom_executes (g : BitString → ℕ) (v : VertexRecord) (mask out : BitString) (count : ℕ) :
    atom.Executes g (state v mask out count)
      (state v mask ((wordChunk (encodeVertex v)).reverse++out) (count+1))
      (20*v.layer+20*v.track+14*v.cut.index+113) := by
  apply rename_executes_to DescriptorAtom.program atomEmbedding g (DescriptorAtom.program_executes g v out count)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hn : ¬i.val<8 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
    simp only [state,hn,↓reduceDIte]

lemma advance_executes (g : BitString → ℕ) (v : VertexRecord) (mask out : BitString) (count : ℕ) :
    advance.Executes g (state v mask out count) (state {v with track:=v.track+1} mask out count) 1 := by
  convert push_executes g (2:Fin 9) true (state v mask out count) using 1
  funext i;fin_cases i <;> simp [state,DescriptorAtom.state,List.replicate_succ,DescriptorAtom.tagBits]

lemma selected_executes (g : BitString → ℕ) (v : VertexRecord) (mask out : BitString) (count : ℕ) :
    selected.Executes g (state v mask out count)
      (state {v with track:=v.track+1} mask ((wordChunk (encodeVertex v)).reverse++out) (count+1))
      (20*v.layer+20*v.track+14*v.cut.index+116) := by
  convert seq_executes _ _ g (atom_executes g v mask out count)
    (advance_executes g v mask ((wordChunk (encodeVertex v)).reverse++out) (count+1)) using 1 <;> omega

lemma state_mask (v : VertexRecord) (mask out next : BitString) (count : ℕ) :
    Function.update (state v mask out count) 8 next=state v next out count := by
  funext i;fin_cases i <;> rfl

lemma loop_execution (g : BitString → ℕ) (v : VertexRecord) (mask out : BitString) (count : ℕ) :
    ∃c,WhileExecution (8:Fin 9) advance selected g (state v mask out count)
      (state {v with track:=v.track+mask.length} []
        ((encodeBitList ((records v mask).map encodeVertex)).reverse++out) (count+(records v mask).length)) c ∧
      c≤mask.length*(20*v.layer+20*(v.track+mask.length)+14*v.cut.index+118)+1 := by
  induction mask generalizing v out count with
  | nil => exact ⟨1,by simpa [records] using WhileExecution.empty (stack:=(8:Fin 9)) (B:=advance) (C:=selected) (g:=g) (state v [] out count) rfl,by simp⟩
  | cons b bs ih =>
    cases b
    · obtain ⟨c,hc,hb⟩ := ih {v with track:=v.track+1} out count
      have he := advance_executes g v bs out count
      have hs := WhileExecution.zero (stack:=(8:Fin 9)) (B:=advance) (C:=selected) (g:=g)
        (s:=state v (false::bs) out count) rfl (by rw [state_mask];exact he) hc
      refine ⟨1+1+1+c,?_,?_⟩
      · have ht : v.track+(bs.length+1)=v.track+1+bs.length := by omega
        simpa only [records,Bool.false_eq_true,ite_false,List.nil_append,List.length_cons,ht] using hs
      · simp only [List.length_cons] at *
        nlinarith
    · obtain ⟨c,hc,hb⟩ := ih {v with track:=v.track+1} ((wordChunk (encodeVertex v)).reverse++out) (count+1)
      have he := selected_executes g v bs out count
      have hs := WhileExecution.one (stack:=(8:Fin 9)) (B:=advance) (C:=selected) (g:=g)
        (s:=state v (true::bs) out count) rfl (by rw [state_mask];exact he) hc
      refine ⟨1+(20*v.layer+20*v.track+14*v.cut.index+116)+1+c,?_,?_⟩
      · have ht : v.track+(bs.length+1)=v.track+1+bs.length := by omega
        have hn : count+((records {v with track:=v.track+1} bs).length+1)=count+1+(records {v with track:=v.track+1} bs).length := by omega
        simpa only [records,ite_true,List.singleton_append,List.map_cons,encodeBitList_eq_chunks,List.flatMap_cons,
          List.reverse_append,List.append_assoc,List.length_cons,ht,hn] using hs
      · simp only [List.length_cons] at *
        nlinarith

lemma records_length_le (v : VertexRecord) (mask : BitString) : (records v mask).length≤mask.length := by
  induction mask generalizing v with
  | nil => simp [records]
  | cons b bs ih => cases b <;> simp only [records,Bool.false_eq_true,ite_false,ite_true,List.nil_append,List.singleton_append,List.length_cons] <;> have := ih {v with track:=v.track+1} <;> omega

 theorem program_executes (g : BitString → ℕ) (v : VertexRecord) (hv : v.track=0) (mask out : BitString) (count : ℕ) :
    ∃c,program.Executes g (state v mask out count)
      (state v [] ((encodeBitList ((records v mask).map encodeVertex)).reverse++out) (count+(records v mask).length)) c ∧
      c≤mask.length*(20*v.layer+20*mask.length+14*v.cut.index+120)+4 := by
  obtain ⟨c,hc,hb⟩ := loop_execution g v mask out count
  let next := (encodeBitList ((records v mask).map encodeVertex)).reverse++out
  let number := count+(records v mask).length
  have hz : (clear (2:Fin 9)).Executes g (state {v with track:=v.track+mask.length} [] next number)
      (state v [] next number) (mask.length+1) := by
    convert clear_executes g (2:Fin 9) (state {v with track:=v.track+mask.length} [] next number) using 1
    · funext i;fin_cases i <;> simp [state,DescriptorAtom.state,DescriptorAtom.tagBits,hv]
    · simp [state,DescriptorAtom.state,hv]
  refine ⟨_,seq_executes _ _ g (whilePop_executes _ _ _ g hc) hz,?_⟩
  rw [hv,Nat.zero_add] at hb
  nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (whilePop_queryFree _ _ _ (push_queryFree _ _) (seq_queryFree _ _ (rename_queryFree _ _ DescriptorAtom.program_queryFree) (push_queryFree _ _)))
  (clear_queryFree _)

end HiddenCircuits.GraphReduction.Runtime.DescriptorMaskRow
