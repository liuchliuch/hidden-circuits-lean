import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateEmitWord

/-! Compute and serialize the positive common denominator even
when the vertex list is empty. A synthetic layer-zero probe uses the same real
signed arithmetic as every ordinary row. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitLengthHeader
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine
open UnitBaselineSetup

def probe : VertexRecord := ⟨false,true,0,0,backgroundCode⟩
noncomputable def seedHeader : OracleBlock 95 := seedFlags [(76,false),(77,true),(60,false),(61,false),(62,false),(63,false)]
noncomputable def program : OracleBlock 95 := seq seedHeader (seq setup (seq arithmetic (seq clean
  (seq (clear 77) UnitCoordinateEmitWord.program))))
noncomputable def bound (width height : ℕ) : ℕ :=
  100*(width+height+1003)^2+UnitBaseline.timePolynomial.eval (width+height+1002)+
    20*(2^16*(width+height+1005))+10000

theorem program_executes (g : BitString → ℕ) (c : QueryContext) (width height : ℕ) :
    ∃t,program.Executes g (initial c width height)
      (initial {c with out:=(wordChunk (signedBits (UnitInterval.commonLength width height))).reverse++c.out} width height) t ∧
      t≤bound width height := by
  let R:=UnitBaselineRow.registers width height probe
  let C:=2^16*(UnitBaseline.inputBound width height probe+3)
  have h1 : seedHeader.Executes g (initial c width height) (parsed c width height probe) 19 := by
    convert seedFlags_executes [(76,false),(77,true),(60,false),(61,false),(62,false),(63,false)] g (initial c width height) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨a,h2,ha⟩:=setup_executes g c width height probe
  obtain ⟨b,h3,hb⟩:=arithmetic_executes g c width height probe
  obtain ⟨d,h4,hd⟩:=clean_executes g c width height probe R
  have h5 : (clear (77:Fin 96)).Executes g (result c width height probe R)
      (SignedScan.state c.n c.row c.col [] c.out c.inner c.outer
        (UnitSignedCallback.params width height c.descriptor) R) 2 := by
    convert clear_executes g (77:Fin 96) (result c width height probe R) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨e,h6,he⟩:=UnitCoordinateEmitWord.program_executes g c width height R C
    (UnitBaseline.result_bounded width height probe)
  have hv : R 2=UnitInterval.commonLength width height := by
    have h:=UnitBaseline.result_value width height probe
    simpa [R,UnitBaselineRow.registers,probe] using h
  rw [hv] at h6
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  dsimp [bound,C,UnitBaseline.inputBound,magnitude,probe,backgroundCode] at *
  nlinarith
lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (seedFlags_queryFree _) (seq_queryFree _ _ setup_queryFree
    (seq_queryFree _ _ (rename_queryFree _ _ UnitBaseline.program_queryFree)
      (seq_queryFree _ _ (clearList_queryFree _) (seq_queryFree _ _ (clear_queryFree _) UnitCoordinateEmitWord.program_queryFree))))
end HiddenCircuits.GraphReduction.Runtime.UnitLengthHeader
