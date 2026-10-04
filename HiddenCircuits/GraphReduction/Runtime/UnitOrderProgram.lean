import HiddenCircuits.GraphReduction.Runtime.UnitOrderMatrixProgram
import HiddenCircuits.GraphReduction.Runtime.UnitOrderCorrect
import HiddenCircuits.GraphReduction.Runtime.UnitOrderBounds
import HiddenCircuits.Approximation.SamplerRuntime.GraphParserProgram

/-! Total raw-graph-to-order execution. Original input bytes, the original
vertex count, and original labels are retained. Rejected inputs return false;
a valid rejected graph may retain its partial component array. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitOrderProgram
open Complexity Complexity.OracleBlock Polynomial DH.Runtime.PairCheck
open HiddenCircuits.Approximation.SamplerRuntime

def accepts (raw : BitString) : Bool :=
  match GraphInput.decode raw with
  | none => false
  | some G => UnitRecognitionRounds.accepts (MatrixData.ofGraph G.2)

def orderBits (raw : BitString) : BitString :=
  match GraphInput.decode raw with
  | none => []
  | some G => UnitOrderRounds.labelBits (UnitOrderSemantics.order (MatrixData.ofGraph G.2))

def input (raw : BitString) : Store 47 := Function.update (fun _=>[]) 0 raw
def parsed (raw : BitString) : Store 47 := fun q =>
  if q.val=0 then raw else if q.val=1 then [(GraphInput.decode raw).isSome]
  else if q.val=2 then (GraphVerifier.parse raw).left
  else if q.val=3 then (GraphVerifier.parse raw).right else []
def ready (raw : BitString) : Store 47 := Function.update (parsed raw) 1 []

def parserEmbedding : Fin 39 ↪ Fin 48 where
  toFun q := ⟨if q.val=2 then 3 else if q.val=3 then 2 else q.val,by split_ifs <;> omega⟩
  inj' := by
    intro q r h;apply Fin.ext;have hh := congrArg Fin.val h
    dsimp only at hh
    split_ifs at hh <;> omega
noncomputable def parser : OracleBlock 47 := rename GraphParser.program parserEmbedding

theorem parser_executes (g : BitString → ℕ) (raw : BitString) :
    ∃t, parser.Executes g (input raw) (parsed raw) t ∧ t≤GraphParser.time.eval raw.length := by
  obtain ⟨t,ht,hb⟩ := GraphParser.program_executes g raw
  refine ⟨t,?_,hb⟩
  apply rename_executes_to GraphParser.program parserEmbedding g ht
  · funext q;fin_cases q <;> rfl
  · funext q;fin_cases q <;> rfl
  · intro q hq
    have h0 : q.val≠0 := by intro h;exact hq 0 (Fin.ext h.symm)
    have h1 : q.val≠1 := by intro h;exact hq 1 (Fin.ext h.symm)
    have h2 : q.val≠2 := by intro h;exact hq 3 (Fin.ext h.symm)
    have h3 : q.val≠3 := by intro h;exact hq 2 (Fin.ext h.symm)
    simp [parsed,input,h0,h1,h2,h3,show q≠0 from fun h=>h0 (congrArg Fin.val h)]

def matrixEmbedding : Fin 46 ↪ Fin 48 where
  toFun q := ⟨q.val+2,by omega⟩
  inj' := by intro q r h;apply Fin.ext;have hh := congrArg Fin.val h;dsimp only at hh;omega
noncomputable def matrix : OracleBlock 47 := UnitOrderMatrixProgram.on matrixEmbedding
noncomputable def trueBranch : OracleBlock 47 := seq matrix (reverseOn 5 1 (by decide))
noncomputable def program : OracleBlock 47 := seq parser
  (branchPop 1 (GraphVerifier.Runtime.writeBool 1 false) (GraphVerifier.Runtime.writeBool 1 false) trueBranch)

def computed (raw : BitString) (G : GraphInput) : Store 47 := fun q =>
  if q.val=0 then raw else if q.val=2 then List.replicate G.1 true
  else if q.val=3 then G.2.bits
  else if q.val=4 then liveBits (UnitRecognitionRounds.run (MatrixData.ofGraph G.2) G.1 (Vector.replicate G.1 true))
  else if q.val=5 then [UnitRecognitionRounds.accepts (MatrixData.ofGraph G.2)]
  else if q.val=47 then UnitOrderRounds.labelBits (UnitOrderSemantics.order (MatrixData.ofGraph G.2)) else []
def completed (raw : BitString) (G : GraphInput) : Store 47 := fun q =>
  if q.val=0 then raw else if q.val=1 then [UnitRecognitionRounds.accepts (MatrixData.ofGraph G.2)]
  else if q.val=2 then List.replicate G.1 true else if q.val=3 then G.2.bits
  else if q.val=4 then liveBits (UnitRecognitionRounds.run (MatrixData.ofGraph G.2) G.1 (Vector.replicate G.1 true))
  else if q.val=47 then UnitOrderRounds.labelBits (UnitOrderSemantics.order (MatrixData.ofGraph G.2)) else []
def output (raw : BitString) : Store 47 :=
  match GraphInput.decode raw with
  | none => Function.update (ready raw) 1 [false]
  | some G => completed raw G

theorem trueBranch_executes (g : BitString → ℕ) (raw : BitString) (G : GraphInput)
    (hg : GraphInput.decode raw=some G) :
    ∃t, trueBranch.Executes g (ready raw) (completed raw G) t ∧ t≤17000*(G.1+1)^7+5 := by
  have fields := GraphParser.output_fields hg
  have hn : (GraphVerifier.parse raw).left=List.replicate G.1 true := fields.1
  have hp : (GraphVerifier.parse raw).right=G.2.bits := fields.2
  obtain ⟨c,hc,hb⟩ := UnitOrderMatrixProgram.on_executes matrixEmbedding g (MatrixData.ofGraph G.2)
    (ready raw) (computed raw G)
    (by funext q;fin_cases q <;> simp [ready,parsed,matrixEmbedding,hn,hp,UnitOrderMatrixProgram.input,MatrixData.ofGraph])
    (by funext q;fin_cases q <;> simp [computed,matrixEmbedding,UnitOrderMatrixProgram.output,
        UnitOrderRounds.run,UnitOrderSemantics.run_remaining,UnitOrderSemantics.order,UnitRecognitionRounds.accepts,MatrixData.ofGraph])
    (by
      intro q hq
      have hlt : q.val<2 := by
        by_contra h
        have hh : 2≤q.val := by omega
        exact hq ⟨q.val-2,by omega⟩ (Fin.ext (by simp [matrixEmbedding];omega))
      have he : q=0 ∨ q=1 := by
        by_cases hz : q.val=0
        · exact Or.inl (Fin.ext hz)
        · right;apply Fin.ext;change q.val=1;omega
      rcases he with rfl|rfl <;> rfl)
  have hf : (reverseOn (5 : Fin 48) 1 (by decide)).Executes g
      (computed raw G) (completed raw G) 3 := by
    convert reverseOn_executes g (5 : Fin 48) 1 (by decide) (computed raw G) using 1
    funext q;fin_cases q <;> simp [computed,completed]
  exact ⟨_,seq_executes _ _ g hc hf,by omega⟩

noncomputable def time : Polynomial ℕ := GraphParser.time+18000*(X+1)^7

/-- Fixed finite-stack execution on every byte string, without a supplied order. -/
theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃t, program.Executes g (input raw) (output raw) t ∧ t≤time.eval raw.length := by
  obtain ⟨c,hc,hb⟩ := parser_executes g raw
  cases hg : GraphInput.decode raw with
  | none =>
    have h := GraphVerifier.Runtime.writeBool_executes (1 : Fin 48) false g (ready raw)
    have hbranch := branchPop_false (1 : Fin 48) (GraphVerifier.Runtime.writeBool 1 false)
      (GraphVerifier.Runtime.writeBool 1 false) trueBranch g
      (s := parsed raw) (rest := []) (by simp [parsed,hg]) h
    refine ⟨c+((ready raw 1).length+4+2)+2,?_,?_⟩
    · simpa only [output,hg] using seq_executes _ _ g hc hbranch
    · simp only [time,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
      have hl : (ready raw 1).length=0 := rfl
      rw [hl]
      nlinarith [Nat.zero_le (raw.length^2),Nat.zero_le (raw.length^3),Nat.zero_le (raw.length^4),
        Nat.zero_le (raw.length^5),Nat.zero_le (raw.length^6),Nat.zero_le (raw.length^7)]
  | some G =>
    obtain ⟨d,hd,db⟩ := trueBranch_executes g raw G hg
    have hbranch := branchPop_true (1 : Fin 48) (GraphVerifier.Runtime.writeBool 1 false)
      (GraphVerifier.Runtime.writeBool 1 false) trueBranch g
      (s := parsed raw) (rest := []) (by simp [parsed,hg]) hd
    refine ⟨c+(d+2)+2,?_,?_⟩
    · simpa only [output,hg] using seq_executes _ _ g hc hbranch
    · have hn := GraphInput.decode_vertices_bound hg
      have hm : 17000*(G.1+1)^7≤17000*(raw.length+1)^7 := by gcongr
      simp only [time,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
      nlinarith [Nat.zero_le (raw.length^2),Nat.zero_le (raw.length^3),Nat.zero_le (raw.length^4),
        Nat.zero_le (raw.length^5),Nat.zero_le (raw.length^6),Nat.zero_le (raw.length^7)]

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ GraphParser.program_queryFree) (branchPop_queryFree _ _ _ _
    (GraphVerifier.Runtime.writeBool_queryFree _ _) (GraphVerifier.Runtime.writeBool_queryFree _ _)
    (seq_queryFree _ _ (UnitOrderMatrixProgram.on_queryFree _) (reverseOn_queryFree _ _ _)))

/-- The concrete output ports preserve the raw input and expose acceptance and order. -/
theorem output_fields (raw : BitString) :
    output raw 0 = raw ∧ output raw 1 = [accepts raw] ∧ output raw 47 = orderBits raw := by
  cases hd : GraphInput.decode raw <;> simp [output,hd,ready,parsed,completed,accepts,orderBits]

theorem accepts_iff (raw : BitString) : accepts raw=true ↔
    ∃G : GraphInput, GraphInput.decode raw=some G ∧ RealUnitInterval.UnitIntervalGraph G.2.graph := by
  cases hd : GraphInput.decode raw with
  | none => simp [accepts,hd]
  | some G => simp [accepts,hd,UnitRecognitionRounds.accepts_ofGraph_iff]

/-- Accepted raw graphs produce their own full original-label umbrella order. -/
theorem accepted_order (raw : BitString) (h : accepts raw=true) :
    ∃G : GraphInput, GraphInput.decode raw=some G ∧
      output raw 47 = UnitOrderRounds.labelBits (UnitOrderSemantics.order (MatrixData.ofGraph G.2)) ∧
      (UnitOrderSemantics.order (MatrixData.ofGraph G.2)).Nodup ∧
      (∀v, v ∈ UnitOrderSemantics.order (MatrixData.ofGraph G.2)) ∧
      UnitIntervalOrder.ListUmbrella G.2.graph (UnitOrderSemantics.order (MatrixData.ofGraph G.2)) := by
  obtain ⟨G,hg,hu⟩ := (accepts_iff raw).mp h
  exact ⟨G,hg,by simp [output,hg,completed],UnitOrderSemantics.order_ofGraph_correct G.2 hu⟩

theorem accepts_malformed (raw : BitString) (h : GraphInput.decode raw=none) : accepts raw=false := by
  simp [accepts,h]

theorem accepts_encode (G : GraphInput) :
    accepts G.encode=true ↔ RealUnitInterval.UnitIntervalGraph G.2.graph := by
  simp [accepts,UnitRecognitionRounds.accepts_ofGraph_iff]

/-- End-to-end graph-to-order execution on an ordinary encoded graph. The
only mathematical input condition is graph-class membership, and the order
is the program's own computed original-label array. -/
theorem program_returns_order (g : BitString → ℕ) (raw : BitString) (G : GraphInput)
    (hg : GraphInput.decode raw=some G) (hu : RealUnitInterval.UnitIntervalGraph G.2.graph) :
    ∃s t, program.Executes g (input raw) s t ∧ t≤time.eval raw.length ∧
      s 0=raw ∧ s 1=[true] ∧ s 2=List.replicate G.1 true ∧ s 3=G.2.bits ∧
      s 47=UnitOrderRounds.labelBits (UnitOrderSemantics.order (MatrixData.ofGraph G.2)) ∧
      (UnitOrderSemantics.order (MatrixData.ofGraph G.2)).Nodup ∧
      (∀v, v ∈ UnitOrderSemantics.order (MatrixData.ofGraph G.2)) ∧
      UnitIntervalOrder.ListUmbrella G.2.graph (UnitOrderSemantics.order (MatrixData.ofGraph G.2)) := by
  obtain ⟨t,ht,hb⟩ := program_executes g raw
  have ha := (UnitRecognitionRounds.accepts_ofGraph_iff G.2).mpr hu
  refine ⟨output raw,t,ht,hb,?_,?_,?_,?_,?_,UnitOrderSemantics.order_ofGraph_correct G.2 hu⟩
  all_goals simp [output,hg,completed,ha]

end HiddenCircuits.GraphReduction.Runtime.UnitOrderProgram
