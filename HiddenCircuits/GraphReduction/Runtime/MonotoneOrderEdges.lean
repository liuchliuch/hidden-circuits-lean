import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderGates

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneOrderRuntime
open Complexity OracleBlock
set_option maxHeartbeats 800000
noncomputable def edges (lower rightPart isLeft : Bool) : OracleBlock 56 := seq (PrivateCut.on callbackForwardEmbedding lower)
  (seq (PrivateCut.on callbackBackwardEmbedding lower) (seq (prepare lower) (boolean lower rightPart isLeft)))

theorem edges_executes (g : BitString→ℕ) (lower rightPart isLeft : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(edges lower rightPart isLeft).Executes g (callbackStore c [] [] [] (recordFields x) (recordFields y) [] [])
      (state lower c x y 7 [outputValue lower rightPart isLeft x y]) t ∧ t≤700*dirSize x y+4100 := by
  let s₀:=callbackStore c [] [] [] (recordFields x) (recordFields y) [] []
  let s₁:=callbackStore c [] [] [] (recordFields x) (recordFields y) [PrivateCut.cut lower x y] []
  let s₂:=callbackStore c [] [] [] (recordFields x) (recordFields y) [PrivateCut.cut lower x y] [PrivateCut.cut lower y x]
  obtain ⟨a,ha,hab⟩:=PrivateCut.on_executes callbackForwardEmbedding g lower x y s₀ (by funext i;fin_cases i <;> rfl)
  have h₁:(PrivateCut.on callbackForwardEmbedding lower).Executes g s₀ s₁ a:=by
    convert ha using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨b,hb,hbb⟩:=PrivateCut.on_executes callbackBackwardEmbedding g lower y x s₁ (by funext i;fin_cases i <;> rfl)
  have h₂:(PrivateCut.on callbackBackwardEmbedding lower).Executes g s₁ s₂ b:=by
    convert hb using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨d,hd,hdb⟩:=prepare_executes g lower c x y
  rw [state_zero] at hd
  have he:=boolean_executes g lower rightPart isLeft c x y
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g hd he)),?_⟩
  have hs:dirSize y x=dirSize x y:=by simp [dirSize,Nat.add_comm]
  rw [hs] at hbb
  omega
lemma edges_queryFree (lower rightPart isLeft : Bool) : (edges lower rightPart isLeft).QueryFree := seq_queryFree _ _ (PrivateCut.on_queryFree _ _)
  (seq_queryFree _ _ (PrivateCut.on_queryFree _ _) (seq_queryFree _ _ (prepare_queryFree _) (boolean_queryFree _ _ _)))
end HiddenCircuits.GraphReduction.Runtime.MonotoneOrderRuntime
