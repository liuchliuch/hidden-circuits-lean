import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateUniform
import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateEmitWord

/-! Literal counted iteration emits every signed endpoint once,
in the descriptor's existing label order. No endpoint list is an input. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRows
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

def state (width height : ℕ) (records : List VertexRecord) (i : ℕ) (out outer : BitString) : Store 95 :=
  UnitBaselineSetup.initial (queryContext records i 0 out [] outer) width height
 def word (width height : ℕ) (records : List VertexRecord) (i : ℕ) : BitString :=
  signedBits (unitCoordinate width height records (records[i]?.getD defaultRecord))
noncomputable def body : OracleBlock 95 := seq UnitCoordinateRow.program
  (seq UnitCoordinateEmitWord.program (push 1 true))
noncomputable def program : OracleBlock 95 := whilePop 6 body body
noncomputable def size (width height : ℕ) (records : List VertexRecord) : ℕ :=
  records.length+(encodeBitList (records.map encodeVertex)).length+width+height
noncomputable def bodyBound (M : ℕ) : ℕ := UnitCoordinateRow.uniformRowBound M+12*UnitCoordinateRow.uniformSizeBound M+33

def output (word : ℕ → BitString) : ℕ → ℕ → BitString → BitString
  | _,0,out => out
  | i,m+1,out => output word (i+1) m ((wordChunk (word i)).reverse++out)

theorem body_executes (g : BitString → ℕ) (width height : ℕ) (records : List VertexRecord)
    (i : ℕ) (out outer : BitString) (hi:i<records.length) :
    ∃t,body.Executes g (state width height records i out outer)
      (state width height records (i+1) ((wordChunk (word width height records i)).reverse++out) outer) t ∧
      t≤bodyBound (size width height records) := by
  let x:=records.get ⟨i,hi⟩
  let c:=queryContext records i 0 out [] outer
  let R:=UnitCoordinateRow.result width height records x
  obtain ⟨a,ha,hba⟩:=UnitCoordinateRow.program_executes width height records g ⟨i,hi⟩ out outer
  have hu:=UnitCoordinateRow.record_uniform width height records ⟨i,hi⟩
  have hR:=UnitCoordinateRow.result_bounded width height records x
  obtain ⟨b,hb,hbb⟩:=UnitCoordinateEmitWord.program_executes g c width height R
    (UnitCoordinateRow.uniformSizeBound (size width height records)) (hR.mono hu.2)
  have hv : R 2=unitCoordinate width height records x := by simp [R,UnitCoordinateRow.result]
  rw [hv] at hb
  have hw : word width height records i=signedBits (unitCoordinate width height records x) := by
    simp [word,x,List.getElem?_eq_getElem hi]
  rw [←hw] at hb
  have hp : (push (1:Fin 96) true).Executes g
      (state width height records i ((wordChunk (word width height records i)).reverse++out) outer)
      (state width height records (i+1) ((wordChunk (word width height records i)).reverse++out) outer) 1 := by
    convert push_executes g (1:Fin 96) true
      (state width height records i ((wordChunk (word width height records i)).reverse++out) outer) using 1
    funext q;fin_cases q <;> simp [state,UnitBaselineSetup.initial,UnitBaselineSetup.state,queryContext,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hp),?_⟩
  dsimp [bodyBound,size] at *
  omega

theorem loop_executes (g : BitString → ℕ) (width height : ℕ) (records : List VertexRecord)
    (i m : ℕ) (out : BitString) (him:i+m≤records.length) :
    ∃t,WhileExecution 6 body body g (state width height records i out (List.replicate m true))
      (state width height records (i+m) (output (word width height records) i m out) []) t ∧
      t≤m*(bodyBound (size width height records)+2)+1 := by
  induction m generalizing i out with
  | zero => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | succ m ih =>
    obtain ⟨a,ha,hba⟩:=body_executes g width height records i out (List.replicate m true) (by omega)
    obtain ⟨b,hb,hbb⟩:=ih (i+1) ((wordChunk (word width height records i)).reverse++out) (by omega)
    have hs : state width height records i out (List.replicate (m+1) true) 6=true::List.replicate m true := by
      simp [state,UnitBaselineSetup.initial,UnitBaselineSetup.state,queryContext,List.replicate_succ]
    have he : Function.update (state width height records i out (List.replicate (m+1) true)) (6:Fin 96) (List.replicate m true)=
        state width height records i out (List.replicate m true) := by funext q;fin_cases q <;> rfl
    have h:=WhileExecution.one hs (by rw [he];exact ha) hb
    refine ⟨1+a+1+b,?_,?_⟩
    · convert h using 1 <;> simp [output,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    · nlinarith

 def rangeWords (word : ℕ → BitString) (i m : ℕ) : List BitString := List.ofFn (fun k:Fin m=>word (i+k.val))
lemma rangeWords_succ (word : ℕ → BitString) (i m : ℕ) :
    rangeWords word i (m+1)=word i::rangeWords word (i+1) m := by
  simp [rangeWords,List.ofFn_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
lemma output_eq (word : ℕ → BitString) (i m : ℕ) (out : BitString) :
    output word i m out=(encodeBitList (rangeWords word i m)).reverse++out := by
  induction m generalizing i out with
  | zero => simp [output,rangeWords,encodeBitList]
  | succ m ih =>
    rw [output,ih,rangeWords_succ]
    simp [encodeBitList_eq_chunks,List.append_assoc]
lemma rangeWords_all (width height : ℕ) (records : List VertexRecord) :
    rangeWords (word width height records) 0 records.length=
      records.map (fun x=>signedBits (unitCoordinate width height records x)) := by
  unfold rangeWords
  have h : (fun k:Fin records.length=>word width height records (0+k.val))=
      (fun k:Fin records.length=>signedBits (unitCoordinate width height records (records.get k))) := by
    funext k;simp [word,List.getElem?_eq_getElem k.isLt]
  rw [h]
  change List.ofFn ((fun x=>signedBits (unitCoordinate width height records x)) ∘ records.get)=_
  rw [←List.map_ofFn,List.ofFn_get]

lemma program_queryFree : program.QueryFree :=
  whilePop_queryFree _ _ _ (seq_queryFree _ _ UnitCoordinateRow.program_queryFree
    (seq_queryFree _ _ UnitCoordinateEmitWord.program_queryFree (push_queryFree _ _)))
    (seq_queryFree _ _ UnitCoordinateRow.program_queryFree (seq_queryFree _ _ UnitCoordinateEmitWord.program_queryFree (push_queryFree _ _)))
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRows
