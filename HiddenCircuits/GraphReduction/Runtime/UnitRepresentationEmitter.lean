import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRows
import HiddenCircuits.GraphReduction.Runtime.UnitLengthHeader
import HiddenCircuits.GraphReduction.Runtime.UnitRepresentationEncoding

/-! The complete finite coordinate encoder computes its signed
common denominator and all signed left endpoints from structural descriptors. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRepresentation
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

 def initial (width height : ℕ) (records : List VertexRecord) : Store 95 :=
  UnitCoordinateRows.state width height records 0 [] []
def finalState (width height : ℕ) (records : List VertexRecord) : Store 95 :=
  Function.update (initial width height records) 7 (bits width height records)
noncomputable def copyOuter : OracleBlock 95 := copyOn 0 6 7 (by decide) (by decide) (by decide)
noncomputable def front : OracleBlock 95 := seq UnitLengthHeader.program (seq copyOuter UnitCoordinateRows.program)
noncomputable def program : OracleBlock 95 := seq front (seq (clear 1) (reverseOn 4 7 (by decide)))
noncomputable def prefixBound (width height : ℕ) (records : List VertexRecord) : ℕ :=
  UnitLengthHeader.bound width height+5*records.length+
    records.length*(UnitCoordinateRows.bodyBound (UnitCoordinateRows.size width height records)+2)+7
noncomputable def bound (width height : ℕ) (records : List VertexRecord) : ℕ :=
  3*prefixBound width height records+2*UnitCoordinateRows.size width height records+records.length+6

theorem prefix_executes (g : BitString → ℕ) (width height : ℕ) (records : List VertexRecord) :
    ∃t,front.Executes g (initial width height records)
      (UnitCoordinateRows.state width height records records.length (bits width height records).reverse []) t ∧
      t≤prefixBound width height records := by
  let header:=(wordChunk (signedBits (UnitInterval.commonLength width height))).reverse
  obtain ⟨a,ha,hba⟩:=UnitLengthHeader.program_executes g (queryContext records 0 0 [] [] []) width height
  have h1 : UnitLengthHeader.program.Executes g (initial width height records)
      (UnitCoordinateRows.state width height records 0 header []) a := by simpa [header,initial,UnitCoordinateRows.state,queryContext] using ha
  have h2 : copyOuter.Executes g (UnitCoordinateRows.state width height records 0 header [])
      (UnitCoordinateRows.state width height records 0 header (List.replicate records.length true)) (5*records.length+2) := by
    convert copyOn_executes g (0:Fin 96) 6 7 (by decide) (by decide) (by decide)
      (UnitCoordinateRows.state width height records 0 header []) rfl using 1
    · funext i;fin_cases i <;> simp [UnitCoordinateRows.state,UnitBaselineSetup.initial,UnitBaselineSetup.state,queryContext]
    · simp [UnitCoordinateRows.state,UnitBaselineSetup.initial,UnitBaselineSetup.state,queryContext]
  obtain ⟨b,hb,hbb⟩:=UnitCoordinateRows.loop_executes g width height records 0 records.length header (by omega)
  have h3:=whilePop_executes _ _ _ g hb
  have he : UnitCoordinateRows.output (UnitCoordinateRows.word width height records) 0 records.length header=
      (bits width height records).reverse := by
    rw [UnitCoordinateRows.output_eq,UnitCoordinateRows.rangeWords_all]
    simp [bits,words,encodeBitList_eq_chunks,header]
  rw [he,Nat.zero_add] at h3
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  unfold prefixBound;omega

lemma initial_bounded (width height : ℕ) (records : List VertexRecord) :
    ∀i,(initial width height records i).length≤UnitCoordinateRows.size width height records := by
  intro i;fin_cases i <;> simp [initial,UnitCoordinateRows.state,UnitBaselineSetup.initial,UnitBaselineSetup.state,
    queryContext,UnitCoordinateRows.size] <;> omega

theorem program_executes (width height : ℕ) (records : List VertexRecord) (g : BitString → ℕ) :
    ∃t,program.Executes g (initial width height records) (finalState width height records) t ∧
      t≤bound width height records := by
  obtain ⟨a,ha,hba⟩:=prefix_executes g width height records
  have hsize:=ha.stack_bound (initial_bounded width height records) (4:Fin 96)
  have hsize' : (bits width height records).length≤UnitCoordinateRows.size width height records+a := by
    simpa [OracleBlock.config,UnitCoordinateRows.state,UnitBaselineSetup.initial,UnitBaselineSetup.state,queryContext] using hsize
  have hc : (clear (1:Fin 96)).Executes g
      (UnitCoordinateRows.state width height records records.length (bits width height records).reverse [])
      (UnitCoordinateRows.state width height records 0 (bits width height records).reverse []) (records.length+1) := by
    convert clear_executes g (1:Fin 96)
      (UnitCoordinateRows.state width height records records.length (bits width height records).reverse []) using 1
    · funext i;fin_cases i <;> rfl
    · simp [UnitCoordinateRows.state,UnitBaselineSetup.initial,UnitBaselineSetup.state,queryContext]
  have hr : (reverseOn (4:Fin 96) 7 (by decide)).Executes g
      (UnitCoordinateRows.state width height records 0 (bits width height records).reverse [])
      (finalState width height records) (2*(bits width height records).length+1) := by
    convert reverseOn_executes g (4:Fin 96) 7 (by decide)
      (UnitCoordinateRows.state width height records 0 (bits width height records).reverse []) using 1
    · funext i;fin_cases i <;> simp [finalState,initial,UnitCoordinateRows.state,UnitBaselineSetup.initial,UnitBaselineSetup.state,queryContext]
    · simp [UnitCoordinateRows.state,UnitBaselineSetup.initial,UnitBaselineSetup.state,queryContext]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hc hr),?_⟩
  unfold bound;omega
lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ UnitLengthHeader.program_queryFree
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) UnitCoordinateRows.program_queryFree))
    (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _))
end HiddenCircuits.GraphReduction.Runtime.UnitRepresentation
