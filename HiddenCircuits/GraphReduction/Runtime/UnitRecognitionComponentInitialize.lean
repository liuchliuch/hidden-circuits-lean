import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentLoop

/-! Physical initialization and full component program from dense matrix,
alive mask, and one original vertex label. All clocks come from the input n. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def emptyData {n : ℕ} (A : Vector Bool n) : Data n := ⟨[],Vector.replicate n false,A⟩
def initial {n : ℕ} (A : Vector Bool n) (root : Fin n) : Data n := advance (emptyData A) root

def input {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (root : Fin n) : Store 36 :=
  Function.update (Function.update (store G A (emptyData A) [] (List.replicate root.val true)
    [] [] [false] [] []) 3 []) 4 []

def initializeEmbedding : Fin 8 ↪ Fin 37 where
  toFun i := ![3,0,35,15,16,17,18,19] i
  inj' := by decide +kernel
noncomputable def initializeMasks : OracleBlock 36 := seq
  (copyOn 2 4 15 (by decide) (by decide) (by decide))
  (seq (push 35 false) (seq (DH.Runtime.WordArray.initializeOn initializeEmbedding) (clear 35)))

lemma allFalseBits (n : ℕ) : liveBits (Vector.replicate n false)=encodeBitList (List.replicate n [false]) := by
  simp [liveBits,liveWords]

theorem initializeMasks_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (root : Fin n) :
    initializeMasks.Executes g (input G A root)
      (store G A (emptyData A) [] (List.replicate root.val true) [] [] [false] [] []) (57*n+19) := by
  let s0 := input G A root
  let s1 := Function.update (store G A (emptyData A) [] (List.replicate root.val true)
    [] [] [false] [] []) (3 : Fin 37) []
  let s2 := Function.update (store G A (emptyData A) [] (List.replicate root.val true)
    [] [] [false] [false] []) (3 : Fin 37) []
  have h1 : (copyOn (2 : Fin 37) 4 15 (by decide) (by decide) (by decide)).Executes g s0 s1 (20*n+2) := by
    convert copyOn_executes g (2 : Fin 37) 4 15 (by decide) (by decide) (by decide) s0 rfl using 1
    · funext i;fin_cases i <;> simp [s0,s1,input,store,UnitRecognitionChoice.rawState,emptyData]
    · simp [s0,input,store,UnitRecognitionChoice.rawState,liveBits_length];ring
  have h2 : (push (35 : Fin 37) false).Executes g s1 s2 1 := by
    convert push_executes g (35 : Fin 37) false s1 using 1
    funext i;fin_cases i <;> rfl
  have h3 := DH.Runtime.WordArray.initializeOn_executes initializeEmbedding g s2 n [false]
    (by funext i;fin_cases i <;> rfl)
  have e3 : Function.update s2 (initializeEmbedding 0) (encodeBitList (List.replicate n [false]))=
      store G A (emptyData A) [] (List.replicate root.val true) [] [] [false] [false] [] := by
    funext i;fin_cases i <;> simp [s2,store,UnitRecognitionChoice.rawState,initializeEmbedding,emptyData,allFalseBits]
  rw [e3] at h3
  have h4 : (clear (35 : Fin 37)).Executes g
      (store G A (emptyData A) [] (List.replicate root.val true) [] [] [false] [false] [])
      (store G A (emptyData A) [] (List.replicate root.val true) [] [] [false] [] []) 2 := by
    convert clear_executes g (35 : Fin 37) _ using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> simp <;> omega

noncomputable def program : OracleBlock 36 := seq initializeMasks
  (seq advanceProgram (seq reset runProgram))
def component {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (root : Fin n) : Data n :=
  run G A n (initial A root)

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (root : Fin n) :
    ∃t, program.Executes g (input G A root)
      (store G A (component G A root) [] [] [] [] [false] [] []) t ∧ t≤2500*(n+1)^5 := by
  have h1 := initializeMasks_executes g G A root
  obtain ⟨c2,h2,b2⟩ := advanceProgram_executes g G A (emptyData A) root [] [] [] [false]
  have h3 := reset_executes g G A (initial A root) [] (List.replicate root.val true) [] [] [false]
  obtain ⟨c4,h4,b4⟩ := runProgram_executes g G A (initial A root)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  have hr := root.isLt
  simp only [List.length_replicate,List.length_cons,List.length_nil]
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5)]

lemma initializeMasks_queryFree : initializeMasks.QueryFree := seq_queryFree _ _
  (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (DH.Runtime.WordArray.initializeOn_queryFree _) (clear_queryFree _)))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ initializeMasks_queryFree
  (seq_queryFree _ _ advanceProgram_queryFree (seq_queryFree _ _ reset_queryFree runProgram_queryFree))

noncomputable def on {k : ℕ} (φ : Fin 37 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 37 ↪ Fin (k+1)) (g : BitString → ℕ)
    {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (root : Fin n) (s t : Store k)
    (hs : s∘φ=input G A root)
    (ht : t∘φ=store G A (component G A root) [] [] [] [] [false] [] [])
    (hf : ∀r,(∀j,φ j≠r) → t r=s r) :
    ∃c, (on φ).Executes g s t c ∧ c≤2500*(n+1)^5 := by
  obtain ⟨c,h,hb⟩ := program_executes g G A root
  exact ⟨c,rename_executes_to program φ g h hs ht hf,hb⟩
lemma on_queryFree {k : ℕ} (φ : Fin 37 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
