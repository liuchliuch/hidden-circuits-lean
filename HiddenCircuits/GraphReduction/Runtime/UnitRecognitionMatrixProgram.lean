import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRounds
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionMaskEmpty

/-! The complete matrix recognizer: initializeMask all labels alive, execute n
residual rounds, and accept exactly when the final physical mask is empty. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionMatrixProgram
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def input {n : ℕ} (G : MatrixData n) : Store 43 := fun r=>
  if r.val=0 then List.replicate n true else if r.val=1 then G.bits else []
def output {n : ℕ} (G : MatrixData n) (A : Vector Bool n) : Store 43 := fun r=>
  if r.val=0 then [A.toList.all Bool.not] else if r.val=1 then G.bits else if r.val=2 then liveBits A else []

def initializeEmbedding : Fin 8 ↪ Fin 44 where
  toFun i := ![2,0,35,15,16,17,18,19] i
  inj' := by decide +kernel
noncomputable def initializeMask : OracleBlock 43 := seq (push 35 true)
  (seq (DH.Runtime.WordArray.initializeOn initializeEmbedding) (clear 35))

theorem initialize_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) :
    initializeMask.Executes g (input G) (UnitRecognitionRounds.state G (Vector.replicate n true) []) (37*n+15) := by
  let s := Function.update (input G) (35 : Fin 44) [true]
  have h1 : (push (35 : Fin 44) true).Executes g (input G) s 1 := push_executes g _ _ _
  have h2 := DH.Runtime.WordArray.initializeOn_executes initializeEmbedding g s n [true]
    (by funext i;fin_cases i <;> rfl)
  have h3 := clear_executes g (35 : Fin 44)
    (Function.update s (initializeEmbedding 0) (encodeBitList (List.replicate n [true])))
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · funext i;fin_cases i <;> simp [input,s,initializeEmbedding,UnitRecognitionRounds.state,liveBits,liveWords]
  · simp [s,input,initializeEmbedding];ring

def emptyEmbedding : Fin 6 ↪ Fin 44 where
  toFun i := ![2,3,4,5,6,7] i
  inj' := by decide +kernel
noncomputable def finish : OracleBlock 43 := seq (UnitRecognitionMaskEmpty.on emptyEmbedding)
  (seq (clear 0) (reverseOn 7 0 (by decide)))

theorem finish_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) (A : Vector Bool n) :
    finish.Executes g (UnitRecognitionRounds.state G A []) (output G A) (50*n+16) := by
  have h1 := UnitRecognitionMaskEmpty.on_executes emptyEmbedding g A.toList (UnitRecognitionRounds.state G A [])
    (by funext i;fin_cases i <;> rfl)
  have h2 := clear_executes g (0 : Fin 44)
    (Function.update (UnitRecognitionRounds.state G A []) (emptyEmbedding 5) [A.toList.all Bool.not])
  have h3 := reverseOn_executes g (7 : Fin 44) 0 (by decide)
    (Function.update (Function.update (UnitRecognitionRounds.state G A []) (emptyEmbedding 5) [A.toList.all Bool.not]) 0 [])
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · funext i;fin_cases i <;> simp [UnitRecognitionRounds.state,emptyEmbedding,output]
  · simp [UnitRecognitionRounds.state,emptyEmbedding];ring

noncomputable def program : OracleBlock 43 := seq initializeMask (seq UnitRecognitionRounds.program finish)

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n) :
    ∃t, program.Executes g (input G)
      (output G (UnitRecognitionRounds.run G n (Vector.replicate n true))) t ∧ t≤15000*(n+1)^7 := by
  obtain ⟨c,hc,hb⟩ := UnitRecognitionRounds.program_executes g G (Vector.replicate n true)
  refine ⟨_,seq_executes _ _ g (initialize_executes g G)
    (seq_executes _ _ g hc (finish_executes g G _)),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5),Nat.zero_le (n^6),Nat.zero_le (n^7)]

lemma initialize_queryFree : initializeMask.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (DH.Runtime.WordArray.initializeOn_queryFree _) (clear_queryFree _))
lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (UnitRecognitionMaskEmpty.on_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ initialize_queryFree
  (seq_queryFree _ _ UnitRecognitionRounds.program_queryFree finish_queryFree)

noncomputable def on {k : ℕ} (φ : Fin 44 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 44 ↪ Fin (k+1)) (g : BitString → ℕ)
    {n : ℕ} (G : MatrixData n) (s t : Store k)
    (hs : s∘φ=input G)
    (ht : t∘φ=output G (UnitRecognitionRounds.run G n (Vector.replicate n true)))
    (hf : ∀r,(∀j,φ j≠r) → t r=s r) :
    ∃c, (on φ).Executes g s t c ∧ c≤15000*(n+1)^7 := by
  obtain ⟨c,h,hb⟩ := program_executes g G
  exact ⟨c,rename_executes_to program φ g h hs ht hf,hb⟩
lemma on_queryFree {k : ℕ} (φ : Fin 44 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionMatrixProgram
