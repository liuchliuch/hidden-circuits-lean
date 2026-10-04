import HiddenCircuits.GraphReduction.Runtime.DescriptorRow

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorRectangle
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

def records (v : VertexRecord) (width : ℕ) : ℕ → List VertexRecord
  | 0 => []
  | n+1 => DescriptorRow.records v width ++ records {v with layer:=v.layer+1} width n

def state (v : VertexRecord) (width rows clock : ℕ) (out : BitString) (count : ℕ) : Store 12 := fun i =>
  if h:i.val<11 then DescriptorRow.state v width [] out count ⟨i.val,h⟩
  else if i.val=11 then List.replicate rows true else List.replicate clock true

def embedding : Fin 11 ↪ Fin 13 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 13 => z.val) h)
noncomputable def row : OracleBlock 12 := rename DescriptorRow.program embedding
noncomputable def body : OracleBlock 12 := seq row (push 1 true)
noncomputable def loop : OracleBlock 12 := whilePop 12 body body
noncomputable def program : OracleBlock 12 := seq (copyOn 11 12 6 (by decide) (by decide) (by decide)) loop

@[simp] lemma records_length (v : VertexRecord) (width n : ℕ) : (records v width n).length=width*n := by
  induction n generalizing v with
  | zero => simp [records]
  | succ n ih => simp [records,ih];ring

lemma body_executes (g : BitString → ℕ) (v : VertexRecord) (hv : v.track=0) (width rows clock : ℕ) (out : BitString) (count : ℕ) :
    ∃c,body.Executes g (state v width rows clock out count)
      (state {v with layer:=v.layer+1} width rows clock
        ((encodeBitList ((DescriptorRow.records v width).map encodeVertex)).reverse++out) (count+width)) c ∧
      c≤width*(20*v.layer+20*width+14*v.cut.index+125)+11 := by
  obtain ⟨c,hc,hb⟩ := DescriptorRow.program_executes g v hv width out count
  have hr : row.Executes g (state v width rows clock out count)
      (state v width rows clock ((encodeBitList ((DescriptorRow.records v width).map encodeVertex)).reverse++out) (count+width)) c := by
    apply rename_executes_to DescriptorRow.program embedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have hni : ¬i.val<11 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
      simp only [state,hni,↓reduceDIte]
  have hp : (push (1:Fin 13) true).Executes g
      (state v width rows clock ((encodeBitList ((DescriptorRow.records v width).map encodeVertex)).reverse++out) (count+width))
      (state {v with layer:=v.layer+1} width rows clock ((encodeBitList ((DescriptorRow.records v width).map encodeVertex)).reverse++out) (count+width)) 1 := by
    convert push_executes g (1:Fin 13) true
      (state v width rows clock ((encodeBitList ((DescriptorRow.records v width).map encodeVertex)).reverse++out) (count+width)) using 1
    funext i;fin_cases i <;> simp [state,DescriptorRow.state,DescriptorMaskRow.state,DescriptorAtom.state,DescriptorAtom.tagBits,List.replicate_succ]
  exact ⟨_,seq_executes _ _ g hr hp,by omega⟩

lemma state_clock (v : VertexRecord) (width rows clock next : ℕ) (out : BitString) (count : ℕ) :
    Function.update (state v width rows clock out count) 12 (List.replicate next true)=state v width rows next out count := by
  funext i;fin_cases i <;> rfl

theorem loop_execution (g : BitString → ℕ) (v : VertexRecord) (hv : v.track=0) (width rows n : ℕ) (out : BitString) (count : ℕ) :
    ∃c,WhileExecution (12:Fin 13) body body g (state v width rows n out count)
      (state {v with layer:=v.layer+n} width rows 0 ((encodeBitList ((records v width n).map encodeVertex)).reverse++out) (count+width*n)) c ∧
      c≤n*(width*(20*(v.layer+n)+20*width+14*v.cut.index+125)+13)+1 := by
  induction n generalizing v out count with
  | zero => exact ⟨1,by simpa [records] using WhileExecution.empty (stack:=(12:Fin 13)) (B:=body) (C:=body) (g:=g) (state v width rows 0 out count) rfl,by simp⟩
  | succ n ih =>
    obtain ⟨a,ha,hab⟩ := body_executes g v hv width rows n out count
    obtain ⟨b,hb,hbb⟩ := ih {v with layer:=v.layer+1} hv
      ((encodeBitList ((DescriptorRow.records v width).map encodeVertex)).reverse++out) (count+width)
    have hs := WhileExecution.one (stack:=(12:Fin 13)) (B:=body) (C:=body) (g:=g)
      (s:=state v width rows (n+1) out count) rfl (by rw [state_clock];exact ha) hb
    refine ⟨1+a+1+b,?_,?_⟩
    · have hl : v.layer+(n+1)=v.layer+1+n := by omega
      have hn : count+width*(n+1)=count+width+width*n := by ring
      simpa only [records,List.map_append,encodeBitList_append,List.reverse_append,List.append_assoc,hl,hn] using hs
    · have hm : width*(20*v.layer+20*width+14*v.cut.index+125)≤width*(20*(v.layer+(n+1))+20*width+14*v.cut.index+125) := by gcongr;omega
      simp only at hbb
      have hl : v.layer+1+n=v.layer+(n+1) := by omega
      rw [hl] at hbb
      nlinarith

theorem program_executes (g : BitString → ℕ) (v : VertexRecord) (hv : v.track=0) (width rows : ℕ) (out : BitString) (count : ℕ) :
    ∃c,program.Executes g (state v width rows 0 out count)
      (state {v with layer:=v.layer+rows} width rows 0 ((encodeBitList ((records v width rows).map encodeVertex)).reverse++out) (count+width*rows)) c ∧
      c≤rows*(width*(20*(v.layer+rows)+20*width+14*v.cut.index+125)+18)+5 := by
  have hc : (copyOn (11:Fin 13) 12 6 (by decide) (by decide) (by decide)).Executes g
      (state v width rows 0 out count) (state v width rows rows out count) (5*rows+2) := by
    convert copyOn_executes g (11:Fin 13) 12 6 (by decide) (by decide) (by decide) (state v width rows 0 out count) rfl using 1
    · funext i;fin_cases i <;> simp [state,DescriptorRow.state,DescriptorMaskRow.state,DescriptorAtom.state]
    · simp [state]
  obtain ⟨c,hl,hb⟩ := loop_execution g v hv width rows rows out count
  exact ⟨_,seq_executes _ _ g hc (whilePop_executes _ _ _ g hl),by nlinarith⟩
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (whilePop_queryFree _ _ _ (seq_queryFree _ _ (rename_queryFree _ _ DescriptorRow.program_queryFree) (push_queryFree _ _))
    (seq_queryFree _ _ (rename_queryFree _ _ DescriptorRow.program_queryFree) (push_queryFree _ _)))
end HiddenCircuits.GraphReduction.Runtime.DescriptorRectangle
