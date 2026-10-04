import HiddenCircuits.GraphReduction.Runtime.DescriptorMaskRow

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorRow
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 600000

def records (v : VertexRecord) (width : ℕ) : List VertexRecord := DescriptorMaskRow.records v (List.replicate width true)
def state (v : VertexRecord) (width : ℕ) (mask out : BitString) (count : ℕ) : Store 10 := fun i =>
  if h:i.val<9 then DescriptorMaskRow.state v mask out count ⟨i.val,h⟩ else if i.val=9 then List.replicate width true else []
def embedding : Fin 9 ↪ Fin 11 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 11 => z.val) h)
noncomputable def program : OracleBlock 10 := seq (copyOn 9 8 6 (by decide) (by decide) (by decide))
  (rename DescriptorMaskRow.program embedding)

@[simp] lemma records_length (v : VertexRecord) (width : ℕ) : (records v width).length=width := by
  induction width generalizing v with
  | zero => rfl
  | succ n ih =>
    change (DescriptorMaskRow.records v (true::List.replicate n true)).length=n+1
    simpa only [DescriptorMaskRow.records,ite_true,List.singleton_append,List.length_cons] using congrArg (fun n=>n+1) (ih {v with track:=v.track+1})

theorem program_executes (g : BitString → ℕ) (v : VertexRecord) (hv : v.track=0) (width : ℕ) (out : BitString) (count : ℕ) :
    ∃c,program.Executes g (state v width [] out count)
      (state v width [] ((encodeBitList ((records v width).map encodeVertex)).reverse++out) (count+width)) c ∧
      c≤width*(20*v.layer+20*width+14*v.cut.index+125)+8 := by
  have hc : (copyOn (9:Fin 11) 8 6 (by decide) (by decide) (by decide)).Executes g
      (state v width [] out count) (state v width (List.replicate width true) out count) (5*width+2) := by
    convert copyOn_executes g (9:Fin 11) 8 6 (by decide) (by decide) (by decide) (state v width [] out count) rfl using 1
    · funext i;fin_cases i <;> simp [state,DescriptorMaskRow.state,DescriptorAtom.state]
    · simp [state]
  obtain ⟨c,hr,hb⟩ := DescriptorMaskRow.program_executes g v hv (List.replicate width true) out count
  have hlen : (DescriptorMaskRow.records v (List.replicate width true)).length=width := records_length v width
  rw [hlen] at hr
  have he : (rename DescriptorMaskRow.program embedding).Executes g
      (state v width (List.replicate width true) out count)
      (state v width [] ((encodeBitList ((records v width).map encodeVertex)).reverse++out) (count+width)) c := by
    apply rename_executes_to DescriptorMaskRow.program embedding g hr
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have hv : ¬i.val<9 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
      simp only [state,hv,↓reduceDIte]
  refine ⟨_,seq_executes _ _ g hc he,?_⟩
  simp only [List.length_replicate] at hb
  nlinarith
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (rename_queryFree _ _ DescriptorMaskRow.program_queryFree)
end HiddenCircuits.GraphReduction.Runtime.DescriptorRow
