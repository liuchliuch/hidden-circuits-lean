import HiddenCircuits.DH.Runtime.PairCheckTest
import HiddenCircuits.DH.Runtime.PairCheckChoice

/-! Pendant-first checking by a fixed query-free finite bit-stack program. -/
namespace HiddenCircuits.DH.Runtime.PairCheck
open Complexity Complexity.OracleBlock

/-- Public ports 0–5: unary size, matrix, live marks, keep index, removed index,
action kind. All remaining ports are temporary. -/
def state (n u v : ℕ) (payload marks output p t edge : BitString) : Store 25 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then payload else if i.val=2 then marks else
  if i.val=3 then List.replicate u true else if i.val=4 then List.replicate v true else if i.val=5 then output else
  if i.val=6 then p else if i.val=7 then t else if i.val=8 then edge else []
def store (n u v : ℕ) (payload marks output : BitString) : Store 25 := state n u v payload marks output [] [] []

def pendantEmbedding : Fin 23 ↪ Fin 26 where
  toFun i := ⟨if i.val<5 then i.val else if i.val=5 then 6 else i.val+3,by split_ifs <;> omega⟩
  inj' := by
    intro i j h;apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    split_ifs at hv <;> omega

def twinEmbedding : Fin 23 ↪ Fin 26 where
  toFun i := ⟨if i.val<5 then i.val else if i.val=5 then 7 else i.val+3,by split_ifs <;> omega⟩
  inj' := by
    intro i j h;apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    split_ifs at hv <;> omega

def edgeEmbedding : Fin 9 ↪ Fin 26 where
  toFun i := ![0,3,4,1,8,9,10,11,12] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def choiceEmbedding : Fin 4 ↪ Fin 26 where
  toFun i := ![6,7,8,5] i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def pendantTest : OracleBlock 25 := rename (TestRuntime.program false) pendantEmbedding
noncomputable def twinTest : OracleBlock 25 := rename (TestRuntime.program true) twinEmbedding
noncomputable def edgeRead : OracleBlock 25 := GraphVerifier.Runtime.matrixLookupOn edgeEmbedding
noncomputable def choose : OracleBlock 25 := rename choice choiceEmbedding
noncomputable def program : OracleBlock 25 := seq pendantTest (seq twinTest (seq edgeRead choose))

def rawResult {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (u v : Fin n) : BitString :=
  chooseBits (test false G alive u v) (test true G alive u v) (G.edge u v)

lemma pendantTest_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) :
    ∃c, pendantTest.Executes g (store n u.val v.val G.bits (liveBits alive) [])
      (state n u.val v.val G.bits (liveBits alive) [] [test false G alive u v] [] []) c ∧ c≤1000*(n+1)^3 := by
  obtain ⟨c,hc,hb⟩ := TestRuntime.program_executes false g G alive u v
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (TestRuntime.program false) pendantEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 5 rfl).elim

lemma twinTest_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (p : BitString) :
    ∃c, twinTest.Executes g (state n u.val v.val G.bits (liveBits alive) [] p [] [])
      (state n u.val v.val G.bits (liveBits alive) [] p [test true G alive u v] []) c ∧ c≤1000*(n+1)^3 := by
  obtain ⟨c,hc,hb⟩ := TestRuntime.program_executes true g G alive u v
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (TestRuntime.program true) twinEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 5 rfl).elim

lemma edgeRead_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (p t : BitString) :
    ∃c, edgeRead.Executes g (state n u.val v.val G.bits (liveBits alive) [] p t [])
      (state n u.val v.val G.bits (liveBits alive) [] p t [G.edge u v]) c ∧ c≤100*(n+1)^2 := by
  have hc := GraphVerifier.Runtime.matrixLookupOn_executes edgeEmbedding g
    (state n u.val v.val G.bits (liveBits alive) [] p t []) n u.val v.val G.bits
    (by funext i;fin_cases i <;> rfl)
  refine ⟨GraphVerifier.Runtime.matrixLookupCost n u.val v.val G.bits,?_,?_⟩
  · convert hc using 1
    funext i;fin_cases i <;> simp [state,edgeEmbedding,matrix_bit]
  · have hb := GraphVerifier.Runtime.matrixLookupCost_in_range n u.val v.val G.bits u.isLt v.isLt
    nlinarith

lemma choose_executes (g : BitString → ℕ) (n u v : ℕ) (payload marks : BitString) (p t e : Bool) :
    ∃c, choose.Executes g (state n u v payload marks [] [p] [t] [e])
      (store n u v payload marks (chooseBits p t e)) c ∧ c≤11 := by
  obtain ⟨c,hc,hb⟩ := choice_executes g p t e
  refine ⟨c,?_,hb⟩
  apply rename_executes_to choice choiceEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim

/-- Operational correctness holds for arbitrary full Boolean matrices, including
nonsymmetric matrices and matrices with self-loops. -/
theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) :
    ∃c, program.Executes g (store n u.val v.val G.bits (liveBits alive) [])
      (store n u.val v.val G.bits (liveBits alive) (rawResult G alive u v)) c ∧ c≤2200*(n+1)^3 := by
  obtain ⟨a,ha,hba⟩ := pendantTest_executes g G alive u v
  obtain ⟨b,hb,hbb⟩ := twinTest_executes g G alive u v [test false G alive u v]
  obtain ⟨c,hc,hbc⟩ := edgeRead_executes g G alive u v [test false G alive u v] [test true G alive u v]
  obtain ⟨d,hd,hbd⟩ := choose_executes g n u.val v.val G.bits (liveBits alive)
    (test false G alive u v) (test true G alive u v) (G.edge u v)
  refine ⟨a+(b+(c+d+2)+2)+2,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hp : (n+1)^2≤(n+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1≤(n+1)^3 := Nat.one_le_pow 3 (n+1) (by omega)
  omega

lemma rawResult_ofGraph {n : ℕ} (G : MatrixGraph n) (alive : Vector Bool n) (u v : Fin n) :
    rawResult (MatrixData.ofGraph G) alive u v=resultBits (PruningModel.tryPair G.graph alive u v) := by
  unfold rawResult
  rw [test_false,test_true]
  cases hp : PruningModel.pendantTest G.graph alive u v <;>
    cases ht : PruningModel.twinTest G.graph alive u v <;>
    simp [chooseBits,resultBits,PruningModel.tryPair,hp,ht,kindBits] <;>
    simp [MatrixData.ofGraph,MatrixGraph.graph]

/-- Exact refinement of the pendant-first semantic pair test. -/
theorem program_executes_graph (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n)
    (alive : Vector Bool n) (u v : Fin n) :
    ∃c, program.Executes g (store n u.val v.val G.bits (liveBits alive) [])
      (store n u.val v.val G.bits (liveBits alive) (resultBits (PruningModel.tryPair G.graph alive u v))) c ∧
      c≤2200*(n+1)^3 := by
  have h := program_executes g (MatrixData.ofGraph G) alive u v
  rw [rawResult_ofGraph] at h
  exact h

/-- A mere length check supplies the complete unconditional operational premise. -/
theorem program_executes_payload (g : BitString → ℕ) (n : ℕ) (payload : BitString)
    (hp : payload.length=n*n) (alive : Vector Bool n) (u v : Fin n) :
    ∃c, program.Executes g (store n u.val v.val payload (liveBits alive) [])
      (store n u.val v.val payload (liveBits alive) (rawResult (MatrixData.ofPayload n payload hp) alive u v)) c ∧
      c≤2200*(n+1)^3 :=
  program_executes g (MatrixData.ofPayload n payload hp) alive u v

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (rename_queryFree _ _ (TestRuntime.program_queryFree false)) (seq_queryFree _ _
    (rename_queryFree _ _ (TestRuntime.program_queryFree true)) (seq_queryFree _ _
      (GraphVerifier.Runtime.matrixLookupOn_queryFree _) (rename_queryFree _ _ choice_queryFree)))


noncomputable def programOn {k : ℕ} (φ : Fin 26 ↪ Fin (k+1)) : OracleBlock k := rename program φ

/-- Arbitrary-stack reuse updates only the action-kind output port. -/
theorem programOn_executes {k : ℕ} (φ : Fin 26 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (u v : Fin n)
    (hs : s∘φ=store n u.val v.val G.bits (liveBits alive) []) :
    ∃c, (programOn φ).Executes g s (Function.update s (φ 5) (rawResult G alive u v)) c ∧
      c≤2200*(n+1)^3 := by
  obtain ⟨c,hc,hb⟩ := program_executes g G alive u v
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g hc hs
  · have he : (Function.update s (φ 5) (rawResult G alive u v))∘φ =
        Function.update (s∘φ) 5 (rawResult G alive u v) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 5).symm _ _

lemma programOn_queryFree {k : ℕ} (φ : Fin 26 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.DH.Runtime.PairCheck
