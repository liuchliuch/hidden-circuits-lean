import HiddenCircuits.GraphReduction.Runtime.CliqueEmitter
import HiddenCircuits.GraphReduction.Runtime.UnitRepresentationSource

/-! Construct both the graph and its signed coordinate payload,
then physically serialize the two words. The only additional cell is stack96. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitSuppliedQuery
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic Polynomial
set_option maxRecDepth 2000
set_option maxHeartbeats 1500000

def bits {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) : BitString :=
  encodeBitList [(unitGraphInput (fun r=>ps.get r) S T s).encode,unitRepresentationBits ps S T s]
def state (n width height : ℕ) (descriptor out saved : BitString) : Store 96 := fun i=>
  if i.val=0 then List.replicate n true else if i.val=7 then out else if i.val=8 then descriptor else
  if i.val=57 then List.replicate width true else if i.val=58 then List.replicate height true else
  if i.val=96 then saved else []
def packetState (n width height : ℕ) (descriptor out saved accum : BitString) : Store 96 :=
  Function.update (state n width height descriptor out saved) 4 accum

def graphMap : Fin 57 ↪ Fin 97 where
  toFun i:=⟨i.val,by omega⟩
  inj':=by intro i j h;exact Fin.ext (congrArg (fun q:Fin 97=>q.val) h)
def coordinateMap : Fin 96 ↪ Fin 97 where
  toFun i:=⟨i.val,by omega⟩
  inj':=by intro i j h;exact Fin.ext (congrArg (fun q:Fin 97=>q.val) h)
def wordMap (graph : Bool) : Fin 2 ↪ Fin 97 where
  toFun i:=if i=0 then (if graph then 96 else 7) else 4
  inj':=by cases graph <;> decide +kernel

noncomputable def graph : OracleBlock 96 := rename (CliqueEmitter.program false) graphMap
noncomputable def save : OracleBlock 96 := moveOn 7 96 9 (by decide) (by decide) (by decide)
noncomputable def coordinates : OracleBlock 96 := rename UnitRepresentation.program coordinateMap
noncomputable def packet : OracleBlock 96 := seq (rename wordEmit (wordMap true))
  (seq (rename wordEmit (wordMap false)) (reverseOn 4 7 (by decide)))
noncomputable def program : OracleBlock 96 := seq graph (seq save (seq coordinates packet))
noncomputable def timePolynomial : Polynomial ℕ :=
  17*CliqueEmitter.time+11*UnitRepresentation.timePolynomial+26*X+38

theorem packet_executes (g : BitString → ℕ) (n width height : ℕ) (descriptor graphBytes coordinates : BitString) :
    packet.Executes g (state n width height descriptor coordinates graphBytes)
      (state n width height descriptor (encodeBitList [graphBytes,coordinates]) [])
      (10*graphBytes.length+10*coordinates.length+27) := by
  let s1:=packetState n width height descriptor coordinates [] (wordChunk graphBytes).reverse
  let s2:=packetState n width height descriptor [] [] ((wordChunk coordinates).reverse++(wordChunk graphBytes).reverse)
  have h1 : (rename wordEmit (wordMap true)).Executes g (state n width height descriptor coordinates graphBytes) s1
      (6*graphBytes.length+7) := by
    apply rename_executes_to _ (wordMap true) g (wordEmit_executes g graphBytes [])
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [s1,packetState,state,wordMap,wordEmitStore] <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  have h2 : (rename wordEmit (wordMap false)).Executes g s1 s2 (6*coordinates.length+7) := by
    apply rename_executes_to _ (wordMap false) g (wordEmit_executes g coordinates (wordChunk graphBytes).reverse)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  have h3 : (reverseOn (4:Fin 97) 7 (by decide)).Executes g s2
      (state n width height descriptor (encodeBitList [graphBytes,coordinates]) [])
      (2*((wordChunk coordinates).length+(wordChunk graphBytes).length)+1) := by
    convert reverseOn_executes g (4:Fin 97) 7 (by decide) s2 using 1
    · funext i;fin_cases i <;> simp [s2,packetState,state,encodeBitList_eq_chunks]
    · simp [s2,packetState]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  simp [wordChunk];omega

lemma coordinate_input_eq (width height : ℕ) (records : List VertexRecord) (saved : BitString) :
    state records.length width height (encodeBitList (records.map encodeVertex)) [] saved ∘ coordinateMap=
      UnitRepresentation.initial width height records := by
  funext i;fin_cases i <;> rfl
lemma coordinate_output_eq (width height : ℕ) (records : List VertexRecord) (out saved : BitString) :
    state records.length width height (encodeBitList (records.map encodeVertex)) out saved ∘ coordinateMap=
      Function.update (UnitRepresentation.initial width height records) 7 out := by
  funext i;fin_cases i <;> rfl

 theorem program_executes {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) (g : BitString → ℕ) :
    ∃t,program.Executes g
      (state (unitGraphInput (fun r=>ps.get r) S T s).1 (2*p) ps.length (unitDescriptor (fun r=>ps.get r) S T s) [] [])
      (state (unitGraphInput (fun r=>ps.get r) S T s).1 (2*p) ps.length (unitDescriptor (fun r=>ps.get r) S T s) (bits ps S T s) []) t ∧
      t≤timePolynomial.eval ((unitGraphInput (fun r=>ps.get r) S T s).1+
        (unitDescriptor (fun r=>ps.get r) S T s).length+2*p+ps.length) := by
  let G:=unitGraphInput (fun r=>ps.get r) S T s
  let D:=unitDescriptor (fun r=>ps.get r) S T s
  let C:=unitRepresentationBits ps S T s
  let M:=G.1+D.length+2*p+ps.length
  obtain ⟨a,ha,hba⟩:=CliqueEmitter.program_polynomial g false (fun r=>ps.get r) S T s
  have h1 : graph.Executes g (state G.1 (2*p) ps.length D [] []) (state G.1 (2*p) ps.length D G.encode []) a := by
    apply rename_executes_to _ graphMap g ha
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 7 rfl).elim
  have hG : G.encode.length≤M+a := by
    have h:=h1.stack_bound (n:=M) (by
      intro i;fin_cases i <;> simp [OracleBlock.config,state,M] <;> omega) (7:Fin 97)
    change G.encode.length≤M+a at h
    exact h
  have h2 : save.Executes g (state G.1 (2*p) ps.length D G.encode [])
      (state G.1 (2*p) ps.length D [] G.encode) (6*G.encode.length+5) := by
    convert moveOn_executes g (7:Fin 97) 96 9 (by decide) (by decide) (by decide)
      (state G.1 (2*p) ps.length D G.encode []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  obtain ⟨b,hb,hbb⟩:=UnitRepresentation.query_executes ps S T s g
  have h3 : coordinates.Executes g (state G.1 (2*p) ps.length D [] G.encode)
      (state G.1 (2*p) ps.length D C G.encode) b := by
    apply rename_executes_to _ coordinateMap g hb
    · simpa only [unitRecords_length] using coordinate_input_eq (2*p) ps.length (unitRecords (fun r=>ps.get r) S T s) G.encode
    · simpa only [unitRecords_length] using coordinate_output_eq (2*p) ps.length (unitRecords (fun r=>ps.get r) S T s) C G.encode
    · clear ha hb h1 h2
      intro i hi
      have he:i.val=96 := by
        by_contra hn;exact hi ⟨i.val,by omega⟩ (Fin.ext rfl)
      have he':i=96:=Fin.ext he
      subst i;rfl
  have hC : C.length≤M+b := by
    have h:=hb.stack_bound (UnitRepresentation.initial_bounded (2*p) ps.length (unitRecords (fun r=>ps.get r) S T s)) (7:Fin 96)
    change C.length≤UnitCoordinateRows.size (2*p) ps.length (unitRecords (fun r=>ps.get r) S T s)+b at h
    simpa only [UnitCoordinateRows.size,unitRecords_length] using h
  have h4:=packet_executes g G.1 (2*p) ps.length D G.encode C
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  have hm:=polynomial_nat_eval_mono CliqueEmitter.time (show G.1+D.length≤M by dsimp [M];omega)
  dsimp only at hm
  change a≤CliqueEmitter.time.eval (G.1+D.length) at hba
  change b≤UnitRepresentation.timePolynomial.eval M at hbb
  change _≤timePolynomial.eval M
  simp only [timePolynomial,eval_add,eval_mul,eval_ofNat,eval_X]
  omega
lemma program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ (CliqueEmitter.program_queryFree false))
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _
      (rename_queryFree _ _ UnitRepresentation.program_queryFree) (seq_queryFree _ _
        (rename_queryFree _ _ wordEmit_queryFree) (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree) (reverseOn_queryFree _ _ _)))))
end HiddenCircuits.GraphReduction.Runtime.UnitSuppliedQuery
