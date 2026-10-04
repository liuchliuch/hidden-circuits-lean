import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! A clean canonical word reader, compiled from the actual self-delimiting
parser; its real cost is independent of the unread tail. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionLabelRead
open Complexity Complexity.OracleBlock GraphVerifier GraphVerifier.Runtime

lemma pairCost (x y : BitString) : parseCost (pairBits x y)=3*x.length+2 := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairBits,parseCost,ih];omega

noncomputable def program : OracleBlock 3 := seq unpairBlock (clear 3)

theorem program_executes (g : BitString → ℕ) (word rest : BitString) :
    program.Executes g (parseStore (pairBits word rest) [] [] [])
      (parseStore rest word [] []) (5*word.length+7) := by
  have h1 := unpairBlock_executes g (pairBits word rest)
  simp only [parse_pair,pairCost] at h1
  have h2 : (clear (3 : Fin 4)).Executes g (parseStore rest word [] [true])
      (parseStore rest word [] []) 2 := by
    convert clear_executes g (3 : Fin 4) _ using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ unpairBlock_queryFree (clear_queryFree _)
noncomputable def on {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s t : Store k) (word rest : BitString)
    (hs : s∘φ=parseStore (pairBits word rest) [] [] [])
    (ht : t∘φ=parseStore rest word [] [])
    (hf : ∀r,(∀j,φ j≠r) → t r=s r) :
    (on φ).Executes g s t (5*word.length+7) :=
  rename_executes_to program φ g (program_executes g word rest) hs ht hf
lemma on_queryFree {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionLabelRead
