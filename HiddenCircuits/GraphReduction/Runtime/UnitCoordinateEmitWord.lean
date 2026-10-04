import HiddenCircuits.GraphReduction.Runtime.UnitCorrectionCallbackDefs
import HiddenCircuits.GraphReduction.Runtime.UnitBaselineRow
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! Serialize the actual signed result register, then erase the
entire arithmetic bank. The accumulated stream is kept reversed until finish. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateEmitWord
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

def wordMap : Fin 2 ↪ Fin 96 where
  toFun i:=if i=0 then 91 else 4
  inj':=by decide +kernel
noncomputable def emit : OracleBlock 95 := rename wordEmit wordMap
def cleanPorts : List (Fin 96) := [89,90,92,93,94,95]
noncomputable def program : OracleBlock 95 := seq emit (clearList cleanPorts)

theorem program_executes (g : BitString → ℕ) (c : QueryContext) (width height : ℕ)
    (R : Fin 7 → ℤ) (C : ℕ) (hR:Bounded C R) :
    ∃t,program.Executes g
      (SignedScan.state c.n c.row c.col [] c.out c.inner c.outer (UnitSignedCallback.params width height c.descriptor) R)
      (UnitBaselineSetup.initial {c with out:=(wordChunk (signedBits (R 2))).reverse++c.out} width height) t ∧
      t≤12*C+28 := by
  let s:=SignedScan.state c.n c.row c.col [] c.out c.inner c.outer (UnitSignedCallback.params width height c.descriptor) R
  let mid:=Function.update (Function.update s (91:Fin 96) []) (4:Fin 96) ((wordChunk (signedBits (R 2))).reverse++c.out)
  have h1 : emit.Executes g s mid (6*(signedBits (R 2)).length+7) := by
    apply rename_executes_to _ wordMap g (wordEmit_executes g (signedBits (R 2)) c.out)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      simp only [mid,Function.update_apply]
      have h4:i≠4:=fun h=>hi 1 h.symm
      have h91:i≠91:=fun h=>hi 0 h.symm
      simp [h4,h91]
  obtain ⟨t,ht,hb⟩:=clearList_executes_local g cleanPorts mid C (by
    intro i hi;simp only [cleanPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hR 0
    · exact hR 1
    · exact hR 3
    · exact hR 4
    · exact hR 5
    · exact hR 6)
  have he : eraseStore cleanPorts mid=UnitBaselineSetup.initial
      {c with out:=(wordChunk (signedBits (R 2))).reverse++c.out} width height := by
    funext i;fin_cases i <;> rfl
  rw [he] at ht
  refine ⟨_,seq_executes _ _ g h1 ht,?_⟩
  have h2:=hR 2
  simp only [cleanPorts,List.length_cons,List.length_nil] at hb
  omega
lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree) (clearList_queryFree _)
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateEmitWord
