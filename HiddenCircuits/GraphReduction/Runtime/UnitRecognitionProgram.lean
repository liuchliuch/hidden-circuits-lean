import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionMatrixProgram
import HiddenCircuits.Approximation.SamplerRuntime.GraphParserProgram

/-! Total ordinary-byte unit-interval recognition. The real graph parser rejects
malformed encodings, and valid input runs the original-n finite-stack matrix
algorithm. No ordering, representation, or runtime certificate is supplied. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionProgram
open Complexity Complexity.OracleBlock Polynomial DH.Runtime.PairCheck
open HiddenCircuits.Approximation.SamplerRuntime

def accepts (raw : BitString) : Bool :=
  match GraphInput.decode raw with
  | none => false
  | some G => UnitRecognitionRounds.accepts (MatrixData.ofGraph G.2)

def input (raw : BitString) : Store 45 := Function.update (fun _=>[]) 0 raw
def parsed (raw : BitString) : Store 45 := fun q=>
  if q.val=0 then raw else if q.val=1 then [(GraphInput.decode raw).isSome]
  else if q.val=2 then (GraphVerifier.parse raw).left
  else if q.val=3 then (GraphVerifier.parse raw).right else []
def ready (raw : BitString) : Store 45 := Function.update (parsed raw) 1 []

def parserEmbedding : Fin 39 ↪ Fin 46 where
  toFun q := ⟨if q.val=2 then 3 else if q.val=3 then 2 else q.val,by split_ifs <;> omega⟩
  inj' := by
    intro q r h;apply Fin.ext;have hh := congrArg Fin.val h
    dsimp only at hh
    split_ifs at hh <;> omega
noncomputable def parser : OracleBlock 45 := rename GraphParser.program parserEmbedding

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
    simp [parsed,input,h0,h1,h2,h3,Function.update_apply,show q≠0 from fun h=>h0 (congrArg Fin.val h)]

def matrixEmbedding : Fin 44 ↪ Fin 46 where
  toFun q := ⟨q.val+2,by omega⟩
  inj' := by intro q r h;apply Fin.ext;have hh := congrArg Fin.val h;dsimp only at hh;omega
noncomputable def matrix : OracleBlock 45 := UnitRecognitionMatrixProgram.on matrixEmbedding
noncomputable def trueBranch : OracleBlock 45 := seq matrix (seq (clear 0) (reverseOn 2 0 (by decide)))
noncomputable def program : OracleBlock 45 := seq parser
  (branchPop 1 (GraphVerifier.Runtime.writeBool 0 false) (GraphVerifier.Runtime.writeBool 0 false) trueBranch)

def computed (raw : BitString) (G : GraphInput) : Store 45 := fun q=>
  if q.val=0 then raw else if q.val=2 then [UnitRecognitionRounds.accepts (MatrixData.ofGraph G.2)]
  else if q.val=3 then G.2.bits else if q.val=4 then liveBits
    (UnitRecognitionRounds.run (MatrixData.ofGraph G.2) G.1 (Vector.replicate G.1 true)) else []

theorem trueBranch_executes (g : BitString → ℕ) (raw : BitString) (G : GraphInput)
    (hg : GraphInput.decode raw=some G) :
    ∃s t, trueBranch.Executes g (ready raw) s t ∧ s 0=[accepts raw] ∧
      t≤15000*(G.1+1)^7+raw.length+8 := by
  have fields := GraphParser.output_fields hg
  have hn : (GraphVerifier.parse raw).left=List.replicate G.1 true := fields.1
  have hp : (GraphVerifier.parse raw).right=G.2.bits := fields.2
  obtain ⟨c,hc,hb⟩ := UnitRecognitionMatrixProgram.on_executes matrixEmbedding g (MatrixData.ofGraph G.2)
    (ready raw) (computed raw G)
    (by funext q;fin_cases q <;> simp [ready,parsed,matrixEmbedding,hn,hp,UnitRecognitionMatrixProgram.input,MatrixData.ofGraph])
    (by funext q;fin_cases q <;> rfl)
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
  let s1 := Function.update (computed raw G) (0 : Fin 46) []
  let s2 := Function.update (Function.update s1 (2 : Fin 46) []) 0 [accepts raw]
  have h1 : (clear (0 : Fin 46)).Executes g (computed raw G) s1 (raw.length+1) := clear_executes g _ _
  have h2 : (reverseOn (2 : Fin 46) 0 (by decide)).Executes g s1 s2 3 := by
    convert reverseOn_executes g (2 : Fin 46) 0 (by decide) s1 using 1
    funext q;fin_cases q <;> simp [s1,s2,computed,accepts,hg]
  refine ⟨s2,_,seq_executes _ _ g hc (seq_executes _ _ g h1 h2),by simp [s2],?_⟩
  omega

noncomputable def time : Polynomial ℕ := GraphParser.time+16000*(X+1)^7

theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃s t, program.Executes g (input raw) s t ∧ s 0=Computability.encodeBool (accepts raw) ∧
      t≤time.eval raw.length := by
  obtain ⟨c,hc,hb⟩ := parser_executes g raw
  cases hg : GraphInput.decode raw with
  | none =>
    let s := Function.update (ready raw) (0 : Fin 46) [false]
    have h := GraphVerifier.Runtime.writeBool_executes (0 : Fin 46) false g (ready raw)
    have hbranch := branchPop_false (1 : Fin 46) (GraphVerifier.Runtime.writeBool 0 false)
      (GraphVerifier.Runtime.writeBool 0 false) trueBranch g
      (s := parsed raw) (rest := []) (by simp [parsed,hg]) h
    refine ⟨s,_,seq_executes _ _ g hc hbranch,?_,?_⟩
    · simp [s,accepts,hg,Computability.encodeBool]
    · simp only [time,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
      have hl : (ready raw 0).length=raw.length := rfl
      rw [hl]
      nlinarith [Nat.zero_le (raw.length^2),Nat.zero_le (raw.length^3),Nat.zero_le (raw.length^4),
        Nat.zero_le (raw.length^5),Nat.zero_le (raw.length^6),Nat.zero_le (raw.length^7)]
  | some G =>
    obtain ⟨s,d,hd,ho,db⟩ := trueBranch_executes g raw G hg
    have hbranch := branchPop_true (1 : Fin 46) (GraphVerifier.Runtime.writeBool 0 false)
      (GraphVerifier.Runtime.writeBool 0 false) trueBranch g
      (s := parsed raw) (rest := []) (by simp [parsed,hg]) hd
    refine ⟨s,_,seq_executes _ _ g hc hbranch,ho,?_⟩
    have hn := GraphInput.decode_vertices_bound hg
    have hm : 15000*(G.1+1)^7≤15000*(raw.length+1)^7 := by gcongr
    simp only [time,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
    nlinarith [Nat.zero_le (raw.length^2),Nat.zero_le (raw.length^3),Nat.zero_le (raw.length^4),
      Nat.zero_le (raw.length^5),Nat.zero_le (raw.length^6),Nat.zero_le (raw.length^7)]

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ GraphParser.program_queryFree) (branchPop_queryFree _ _ _ _
    (GraphVerifier.Runtime.writeBool_queryFree _ _) (GraphVerifier.Runtime.writeBool_queryFree _ _)
    (seq_queryFree _ _ (UnitRecognitionMatrixProgram.on_queryFree _)
      (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _))))

theorem polyVerifier : PolyVerifier accepts :=
  polyVerifier_of_block accepts program program_queryFree time (program_executes (fun _=>0))

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionProgram
