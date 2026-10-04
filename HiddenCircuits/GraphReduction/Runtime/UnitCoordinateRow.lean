import HiddenCircuits.GraphReduction.Runtime.UnitBaselineRow
import HiddenCircuits.GraphReduction.Runtime.UnitSignedScanValue

namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRow
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine
open UnitBaselineSetup
set_option maxRecDepth 2000

noncomputable def scans : OracleBlock 95 := seq (UnitSignedScan.program false) (UnitSignedScan.program true)
noncomputable def choose : OracleBlock 95 := branchPop 77 skip scans skip
noncomputable def program : OracleBlock 95 := seq UnitBaselineRow.program choose

def result (width height : ℕ) (records : List VertexRecord) (x : VertexRecord) : Fin 7 → ℤ :=
  Function.update (UnitBaselineRow.registers width height x) 2 (unitCoordinate width height records x)
noncomputable def registerBound (width height : ℕ) (x : VertexRecord) : ℕ := 2^16*(UnitBaseline.inputBound width height x+3)
noncomputable def bound (n L width height : ℕ) (x : VertexRecord) : ℕ :=
  UnitBaselineRow.bound n L width height x+
    UnitSignedScan.bound n L width (registerBound width height x)+
    UnitSignedScan.bound n L width (SignedCounter.counterBound (registerBound width height x) n)+10

 theorem scans_executes (width height : ℕ) (records : List VertexRecord) (g : BitString → ℕ)
    (i : Fin records.length) (out outer : BitString) (R : Fin 7 → ℤ) (C : ℕ)
    (hR : Bounded C R) (h1 : R 5=1) (hneg : R 6=-1) :
    ∃ t, scans.Executes g
      (SignedScan.state records.length i.val 0 [] out [] outer (UnitSignedCallback.params width height (encodeBitList (records.map encodeVertex))) R)
      (SignedScan.state records.length i.val 0 [] out [] outer (UnitSignedCallback.params width height (encodeBitList (records.map encodeVertex)))
        (Function.update R 2 (R 2+(records.map (unitCorrectionValue false width (records.get i))).sum+
          (records.map (unitCorrectionValue true width (records.get i))).sum))) t ∧
      t≤UnitSignedScan.bound records.length (encodeBitList (records.map encodeVertex)).length width C+
        UnitSignedScan.bound records.length (encodeBitList (records.map encodeVertex)).length width (SignedCounter.counterBound C records.length)+2 := by
  obtain ⟨a,ha,hba⟩ := UnitSignedScan.program_executes false width height records g i.val out outer R C hR h1 hneg i.isLt
  let d := SignedScan.total (UnitSignedScan.edge false width records) i.val 0 records.length
  have hr := SignedCounter.bounded_counter R C records.length d hR (SignedScan.total_abs _ _ _ _)
  obtain ⟨b,hb,hbb⟩ := UnitSignedScan.program_executes true width height records g i.val out outer
    (Function.update R 2 (R 2+d)) (SignedCounter.counterBound C records.length) hr (by simpa using h1) (by simpa using hneg) i.isLt
  have hh := seq_executes _ _ g ha hb
  simp only [Function.update_self,Function.update_idem] at hh
  dsimp only [d] at hh
  rw [UnitSignedScan.total_correct false width records i,UnitSignedScan.total_correct true width records i] at hh
  exact ⟨_,hh,by omega⟩

 theorem program_executes (width height : ℕ) (records : List VertexRecord) (g : BitString → ℕ)
    (i : Fin records.length) (out outer : BitString) :
    ∃ t, program.Executes g (UnitBaselineRow.initial (queryContext records i.val 0 out [] outer) width height)
      (SignedScan.state records.length i.val 0 [] out [] outer (UnitSignedCallback.params width height (encodeBitList (records.map encodeVertex)))
        (result width height records (records.get i))) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length width height (records.get i) := by
  let x := records.get i
  let c := queryContext records i.val 0 out [] outer
  let R := UnitBaselineRow.registers width height x
  let C := registerBound width height x
  let params := UnitSignedCallback.params width height (encodeBitList (records.map encodeVertex))
  obtain ⟨a,ha,hba⟩ := UnitBaselineRow.program_executes g records i width height out outer
  have he : Function.update (UnitBaselineRow.finalState c width height x) (77:Fin 96) []=
      SignedScan.state records.length i.val 0 [] out [] outer params R := by
    funext q;fin_cases q <;> rfl
  have hget : UnitBaselineRow.finalState c width height x 77=x.probe::[] := rfl
  have hvalue := UnitBaseline.result_value width height x
  have hconst := UnitBaseline.code_constants (UnitBaseline.mode x) width height x.layer x.track
  have hR : Bounded C R := UnitBaseline.result_bounded width height x
  have h1 : R 5=1 := hconst.1
  have hn : R 6=-1 := hconst.2
  cases hp:x.probe with
  | false =>
    obtain ⟨b,hb,hbb⟩ := scans_executes width height records g i out outer R C hR h1 hn
    have hr : Function.update R 2 (R 2+(records.map (unitCorrectionValue false width x)).sum+
        (records.map (unitCorrectionValue true width x)).sum)=result width height records x := by
      unfold result
      congr 1
      change R 2+_+_=unitCoordinate width height records x
      change R 2=_ at hvalue
      simp only [unitCoordinate,hp,Bool.false_eq_true,ite_false] at hvalue ⊢
      rw [hvalue]
    rw [hr] at hb
    have hc : choose.Executes g (UnitBaselineRow.finalState c width height x)
        (SignedScan.state records.length i.val 0 [] out [] outer params (result width height records x)) (b+2) := by
      apply branchPop_false _ _ _ _ g (by simpa [hp] using hget)
      rw [he]
      exact hb
    refine ⟨_,seq_executes _ _ g ha hc,?_⟩
    unfold bound
    dsimp only [C,x] at *
    omega
  | true =>
    have hr : result width height records x=R := by
      change Function.update R 2 (unitCoordinate width height records x)=R
      change R 2=_ at hvalue
      simp only [hp,ite_true,unitCoordinate] at hvalue ⊢
      rw [←hvalue,Function.update_eq_self]
    have hc : choose.Executes g (UnitBaselineRow.finalState c width height x)
        (SignedScan.state records.length i.val 0 [] out [] outer params (result width height records x)) 3 := by
      apply branchPop_true _ _ _ _ g (by simpa [hp] using hget)
      rw [he,hr]
      exact skip_executes g _
    refine ⟨_,seq_executes _ _ g ha hc,?_⟩
    unfold bound
    omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ UnitBaselineRow.program_queryFree
  (branchPop_queryFree _ _ _ _ skip_queryFree
    (seq_queryFree _ _ (UnitSignedScan.program_queryFree false) (UnitSignedScan.program_queryFree true)) skip_queryFree)

end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRow
