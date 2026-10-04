import HiddenCircuits.GraphReduction.Runtime.UnitOrderRounds
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionMaskEmpty

/-! Initialize the original labels, run the output-producing component rounds,
and expose both the acceptance bit and the accumulated original-label array. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitOrderMatrixProgram
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def input {n : ℕ} (G : MatrixData n) : Store 45 := fun r =>
  if r.val=0 then List.replicate n true else if r.val=1 then G.bits else []
def output {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (acc : List (Fin n)) : Store 45 := fun r =>
  if r.val=0 then List.replicate n true else if r.val=1 then G.bits
  else if r.val=2 then liveBits A else if r.val=3 then [A.toList.all Bool.not]
  else if r.val=45 then UnitOrderRounds.labelBits acc else []

def initializeEmbedding : Fin 8 ↪ Fin 46 where
  toFun i := ![2,0,35,15,16,17,18,19] i
  inj' := by decide +kernel
noncomputable def initializeMask : OracleBlock 45 := seq (push 35 true)
  (seq (DH.Runtime.WordArray.initializeOn initializeEmbedding) (clear 35))

theorem initialize_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) :
    initializeMask.Executes g (input G) (UnitOrderRounds.state G (Vector.replicate n true) [] []) (37*n+15) := by
  let s := Function.update (input G) (35 : Fin 46) [true]
  have h1 : (push (35 : Fin 46) true).Executes g (input G) s 1 := push_executes g _ _ _
  have h2 := DH.Runtime.WordArray.initializeOn_executes initializeEmbedding g s n [true]
    (by funext i;fin_cases i <;> rfl)
  have h3 := clear_executes g (35 : Fin 46)
    (Function.update s (initializeEmbedding 0) (encodeBitList (List.replicate n [true])))
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · funext i;fin_cases i <;> simp [input,s,initializeEmbedding,UnitOrderRounds.state,
      UnitOrderRounds.labelBits,encodeBitList,liveBits,liveWords]
  · simp [s,initializeEmbedding];ring

def emptyEmbedding : Fin 6 ↪ Fin 46 where
  toFun i := ![2,3,4,5,6,7] i
  inj' := by decide +kernel
noncomputable def finish : OracleBlock 45 := seq (UnitRecognitionMaskEmpty.on emptyEmbedding)
  (reverseOn 7 3 (by decide))

theorem finish_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (acc : List (Fin n)) :
    finish.Executes g (UnitOrderRounds.state G A acc []) (output G A acc) (49*n+13) := by
  have h1 := UnitRecognitionMaskEmpty.on_executes emptyEmbedding g A.toList (UnitOrderRounds.state G A acc [])
    (by funext i;fin_cases i <;> rfl)
  have h2 := reverseOn_executes g (7 : Fin 46) 3 (by decide)
    (Function.update (UnitOrderRounds.state G A acc []) (emptyEmbedding 5) [A.toList.all Bool.not])
  convert seq_executes _ _ g h1 h2 using 1
  · funext i;fin_cases i <;> simp [UnitOrderRounds.state,emptyEmbedding,output]
  · simp [emptyEmbedding]

noncomputable def program : OracleBlock 45 := seq initializeMask (seq UnitOrderRounds.program finish)

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) :
    ∃t, program.Executes g (input G)
      (output G (UnitOrderRounds.run G n (Vector.replicate n true) []).1
        (UnitOrderRounds.run G n (Vector.replicate n true) []).2) t ∧ t≤17000*(n+1)^7 := by
  obtain ⟨c,hc,hb⟩ := UnitOrderRounds.program_executes g G (Vector.replicate n true) []
  refine ⟨_,seq_executes _ _ g (initialize_executes g G)
    (seq_executes _ _ g hc (finish_executes g G _ _)),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5),Nat.zero_le (n^6),Nat.zero_le (n^7)]

lemma initialize_queryFree : initializeMask.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (DH.Runtime.WordArray.initializeOn_queryFree _) (clear_queryFree _))
lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (UnitRecognitionMaskEmpty.on_queryFree _)
  (reverseOn_queryFree _ _ _)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ initialize_queryFree
  (seq_queryFree _ _ UnitOrderRounds.program_queryFree finish_queryFree)

noncomputable def on {k : ℕ} (φ : Fin 46 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 46 ↪ Fin (k+1)) (g : BitString → ℕ)
    {n : ℕ} (G : MatrixData n) (s t : Store k)
    (hs : s∘φ=input G)
    (ht : t∘φ=output G (UnitOrderRounds.run G n (Vector.replicate n true) []).1
      (UnitOrderRounds.run G n (Vector.replicate n true) []).2)
    (hf : ∀r,(∀j,φ j≠r) → t r=s r) :
    ∃c, (on φ).Executes g s t c ∧ c≤17000*(n+1)^7 := by
  obtain ⟨c,h,hb⟩ := program_executes g G
  exact ⟨c,rename_executes_to program φ g h hs ht hf,hb⟩
lemma on_queryFree {k : ℕ} (φ : Fin 46 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitOrderMatrixProgram
