import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct

/-! Clean canonical pair parsing, using the actual bit-by-bit unpair machine. -/
namespace HiddenCircuits.Circuit.Runtime.SamplePairParser
open HiddenCircuits.Complexity OracleBlock GraphVerifier.Runtime

noncomputable def block : OracleBlock 3 := seq unpairBlock (clear 3)

theorem block_executes (g : BitString → ℕ) (left right : BitString) :
    block.Executes g (parseStore (pairBits left right) [] [] []) (parseStore right left [] []) (5*left.length+7) := by
  have hu : unpairBlock.Executes g (parseStore (pairBits left right) [] [] [])
      (parseStore right left [] [true]) (5*left.length+3) := by
    convert unpairBlock_executes g (pairBits left right) using 1
    · simp only [GraphVerifier.parse_pair]
    · simp [GraphVerifier.parse_pair,BinaryArithmetic.pair_parse_cost];omega
  have hc : (clear (3:Fin 4)).Executes g (parseStore right left [] [true]) (parseStore right left [] []) 2 := by
    convert clear_executes g (3:Fin 4) (parseStore right left [] [true]) using 1
    funext i;fin_cases i <;> rfl
  have h := seq_executes unpairBlock (clear 3) g hu hc
  simpa only [show 5*left.length+3+2+2=5*left.length+7 by omega] using h

lemma block_queryFree : block.QueryFree := seq_queryFree _ _ unpairBlock_queryFree (clear_queryFree _)

noncomputable def on {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : OracleBlock k := rename block φ

theorem on_executes {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) (g : BitString → ℕ) (left right : BitString)
    (s t : Store k) (hs : s∘φ=parseStore (pairBits left right) [] [] [])
    (ht : t∘φ=parseStore right left [] []) (hf : ∀ j, (∀ i, φ i≠j) → t j=s j) :
    (on φ).Executes g s t (5*left.length+7) := rename_executes_to block φ g (block_executes g left right) hs ht hf

lemma on_queryFree {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ block_queryFree

end HiddenCircuits.Circuit.Runtime.SamplePairParser
