import HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetupHeaders

/-! Descriptor lookup, literal parse, unary signed conversion,
finite affine program selection, and work-bank cleanup for one coordinate. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitBaselineRow
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine
open UnitBaselineSetup

abbrev initial := UnitBaselineSetup.initial
 def registers (width height : ℕ) (x : VertexRecord) : Fin 7 → ℤ :=
  evaluate (UnitBaseline.code (UnitBaseline.mode x)) (UnitBaseline.init width height x.layer x.track)
 def finalState (c : QueryContext) (width height : ℕ) (x : VertexRecord) : Store 95 :=
  UnitBaselineSetup.result c width height x (registers width height x)
noncomputable def program : OracleBlock 95 := seq lookup (seq parse (seq setup (seq arithmetic clean)))
noncomputable def bound (n L width height : ℕ) (x : VertexRecord) : ℕ :=
  lookupBound L n+5*L+100*(magnitude width height x+1)^2+100*magnitude width height x+
    UnitBaseline.timePolynomial.eval (UnitBaseline.inputBound width height x)+4000

 theorem program_executes (g : BitString → ℕ) (records : List VertexRecord) (i : Fin records.length)
    (width height : ℕ) (out outer : BitString) :
    ∃t,program.Executes g (initial (queryContext records i.val 0 out [] outer) width height)
      (finalState (queryContext records i.val 0 out [] outer) width height (records.get i)) t ∧
      t≤bound records.length (encodeBitList (records.map encodeVertex)).length width height (records.get i) := by
  let x:=records.get i
  let c:=queryContext records i.val 0 out [] outer
  obtain ⟨a,ha,hba⟩ := lookup_executes g records i width height out outer
  have hb:=parse_executes g c width height x
  obtain ⟨d,hd,hbd⟩ := setup_executes g c width height x
  obtain ⟨e,he,hbe⟩ := arithmetic_executes g c width height x
  obtain ⟨f,hf,hbf⟩ := clean_executes g c width height x (registers width height x)
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hd (seq_executes _ _ g he hf))),?_⟩
  have hx:=recordParse_cost_le x
  have hL:=descriptor_record_length records i
  unfold bound
  dsimp only [x] at *
  omega

lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (listLookupOn_queryFree _) (seq_queryFree _ _ (rename_queryFree _ _ recordParse_queryFree)
    (seq_queryFree _ _ setup_queryFree (seq_queryFree _ _
      (rename_queryFree _ _ UnitBaseline.program_queryFree) (clearList_queryFree _))))
end HiddenCircuits.GraphReduction.Runtime.UnitBaselineRow
