import HiddenCircuits.GraphReduction.Runtime.CliqueDirected
import HiddenCircuits.GraphReduction.Runtime.MonotoneCallback

namespace HiddenCircuits.GraphReduction.Runtime.CliqueCallback
open Complexity OracleBlock
set_option maxHeartbeats 1000000

def edgeState (c : QueryContext) (x y : VertexRecord) (forward backward layerEq trackEq output : BitString) : Store 56 := fun i =>
  if i.val=35 then layerEq else if i.val=36 then trackEq else callbackStore c output [] [] (recordFields x) (recordFields y) forward backward i

def layerEmbedding : Fin 6 ↪ Fin 57 where
  toFun i := (![17,28,35,37,38,39] : Fin 6 → Fin 57) i
  inj' := by decide +kernel
def trackEmbedding : Fin 6 ↪ Fin 57 where
  toFun i := (![18,29,36,37,38,39] : Fin 6 → Fin 57) i
  inj' := by decide +kernel
def finalEmbedding : Fin 18 ↪ Fin 57 where
  toFun i := (![33,34,11,22,12,23,35,36,37,38,39,40,41,42,43,44,3,45] : Fin 18 → Fin 57) i
  inj' := by decide +kernel

def finalGate (mode : Bool) : List Bool → Bool
  | [forward,backward,ls,rs,lp,rp,layerEq,trackEq] =>
      forward || backward || (layerEq &&
        (if lp || rp then (if mode then decide (ls=rs) else true) && (if lp && rp then !trackEq else true)
        else decide (ls=rs) && !trackEq))
  | _ => false
noncomputable def edges (mode : Bool) : OracleBlock 56 := seq (CliqueDirected.on callbackForwardEmbedding mode)
  (seq (CliqueDirected.on callbackBackwardEmbedding mode)
    (seq (GraphVerifier.Runtime.readLengthOn layerEmbedding)
      (seq (GraphVerifier.Runtime.readLengthOn trackEmbedding) (gate8On finalEmbedding (finalGate mode)))))

theorem edges_executes (g : BitString → ℕ) (mode : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(edges mode).Executes g (callbackStore c [] [] [] (recordFields x) (recordFields y) [] [])
      (edgeState c x y [cliqueDirectedRecordAdj mode x y] [cliqueDirectedRecordAdj mode y x]
        [decide (x.layer=y.layer)] [decide (x.track=y.track)] [cliqueRecordAdj mode x y]) t ∧ t≤600*dirSize x y+2500 := by
  let f := cliqueDirectedRecordAdj mode x y
  let b := cliqueDirectedRecordAdj mode y x
  let s₀ := callbackStore c [] [] [] (recordFields x) (recordFields y) [] []
  let s₁ := callbackStore c [] [] [] (recordFields x) (recordFields y) [f] []
  let s₂ := callbackStore c [] [] [] (recordFields x) (recordFields y) [f] [b]
  let s₃ := edgeState c x y [f] [b] [decide (x.layer=y.layer)] [] []
  let s₄ := edgeState c x y [f] [b] [decide (x.layer=y.layer)] [decide (x.track=y.track)] []
  let s₅ := edgeState c x y [f] [b] [decide (x.layer=y.layer)] [decide (x.track=y.track)] [cliqueRecordAdj mode x y]
  obtain ⟨a,ha,hab⟩ := CliqueDirected.on_executes callbackForwardEmbedding g mode x y s₀ (by funext i;fin_cases i <;> rfl)
  have h₁ : (CliqueDirected.on callbackForwardEmbedding mode).Executes g s₀ s₁ a := by
    convert ha using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨d,hd,hdb⟩ := CliqueDirected.on_executes callbackBackwardEmbedding g mode y x s₁ (by funext i;fin_cases i <;> rfl)
  have h₂ : (CliqueDirected.on callbackBackwardEmbedding mode).Executes g s₁ s₂ d := by
    convert hd using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨l,hl,hlb⟩ := GraphVerifier.Runtime.readLengthOn_executes layerEmbedding g s₂
    (List.replicate x.layer true) (List.replicate y.layer true) (by funext i;fin_cases i <;> rfl)
  simp only [List.length_replicate] at hl hlb
  have h₃ : (GraphVerifier.Runtime.readLengthOn layerEmbedding).Executes g s₂ s₃ l := by
    convert hl using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,hrb⟩ := GraphVerifier.Runtime.readLengthOn_executes trackEmbedding g s₃
    (List.replicate x.track true) (List.replicate y.track true) (by funext i;fin_cases i <;> rfl)
  simp only [List.length_replicate] at hr hrb
  have h₄ : (GraphVerifier.Runtime.readLengthOn trackEmbedding).Executes g s₃ s₄ r := by
    convert hr using 1
    funext i;fin_cases i <;> rfl
  let bits : Fin 8 → Bool := ![f,b,x.side,y.side,x.probe,y.probe,decide (x.layer=y.layer),decide (x.track=y.track)]
  have hf := gate8On_executes finalEmbedding g (finalGate mode) bits s₄ (by funext i;fin_cases i <;> rfl)
  have he : finalGate mode (gate8Args bits)=cliqueRecordAdj mode x y := by
    simp [finalGate,gate8Args,bits,f,b,cliqueRecordAdj,cliqueLocalAdj]
  rw [he] at hf
  have h₅ : (gate8On finalEmbedding (finalGate mode)).Executes g s₄ s₅ 92 := by
    convert hf using 1
    funext i;fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅))),?_⟩
  have hswap : dirSize y x=dirSize x y := by simp [dirSize,Nat.add_comm]
  rw [hswap] at hdb
  have hcoord : x.layer+y.layer+x.track+y.track≤dirSize x y := by simp [dirSize,encodeVertex_length];omega
  omega

lemma edges_queryFree (mode : Bool) : (edges mode).QueryFree := seq_queryFree _ _ (CliqueDirected.on_queryFree _ _)
  (seq_queryFree _ _ (CliqueDirected.on_queryFree _ _) (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _)
    (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _) (gate8On_queryFree _ _))))
end HiddenCircuits.GraphReduction.Runtime.CliqueCallback
