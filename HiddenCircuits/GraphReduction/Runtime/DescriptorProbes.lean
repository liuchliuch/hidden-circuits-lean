import HiddenCircuits.GraphReduction.Runtime.DescriptorEven

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorFront
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 700000

def taggedVertex (side probe : Bool) (layer : ℕ) : VertexRecord := ⟨side,probe,layer,0,backgroundCode⟩
noncomputable def retag (side probe : Bool) : OracleBlock 19 := seq (clear 0) (prepend 0 [side,probe,false,false,false,false])
noncomputable def probes (side : Bool) : OracleBlock 19 := seq (retag side true)
  (seq (rectangle true) (seq (clear 1) (retag false false)))

lemma retag_executes (g : BitString → ℕ) (oldSide oldProbe side probe : Bool)
    (layer width height samples : ℕ) (S T pairs out : BitString) (count : ℕ) :
    (retag side probe).Executes g (workState (taggedVertex oldSide oldProbe layer) width height samples 0 [] S T pairs out count)
      (workState (taggedVertex side probe layer) width height samples 0 [] S T pairs out count) 28 := by
  let start := workState (taggedVertex oldSide oldProbe layer) width height samples 0 [] S T pairs out count
  let a := Function.update start (0:Fin 20) []
  have hc : (clear (0:Fin 20)).Executes g start a 7 := clear_executes g (0:Fin 20) start
  have hp : (prepend (0:Fin 20) [side,probe,false,false,false,false]).Executes g a
      (workState (taggedVertex side probe layer) width height samples 0 [] S T pairs out count) 19 := by
    convert prepend_executes g (0:Fin 20) [side,probe,false,false,false,false] a using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ g hc hp

theorem probes_executes (g : BitString → ℕ) (side : Bool) (width height samples : ℕ)
    (S T pairs out : BitString) (count : ℕ) :
    ∃c,(probes side).Executes g (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs out count)
      (workState (DescriptorEven.vertex 0) width height samples 0 [] S T pairs
        ((encodeBitList ((DescriptorRectangle.records (taggedVertex side true 0) samples height).map encodeVertex)).reverse++out)
        (count+samples*height)) c ∧ c≤height*(samples*(20*height+20*samples+125)+19)+68 := by
  have h₁ := retag_executes g false false side true 0 width height samples S T pairs out count
  obtain ⟨c,h₂,hb⟩ := rectangle_executes g true (taggedVertex side true 0) rfl width height samples S T pairs out count
  let next := (encodeBitList ((DescriptorRectangle.records (taggedVertex side true 0) samples height).map encodeVertex)).reverse++out
  have h₃ := DescriptorEven.clear_layer g (taggedVertex side true height) width height samples 0 S T pairs next (count+samples*height)
  have h₄ := retag_executes g side true false false 0 width height samples S T pairs next (count+samples*height)
  have he : {taggedVertex side true 0 with layer:=(taggedVertex side true 0).layer+height}=taggedVertex side true height := by simp [taggedVertex]
  rw [he] at h₂
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  dsimp only [taggedVertex,backgroundCode] at hb
  simp only [ite_true,Nat.zero_add,Nat.mul_zero,Nat.add_zero] at hb
  change 28+(c+(height+1+28+2)+2)+2≤_
  nlinarith
end HiddenCircuits.GraphReduction.Runtime.DescriptorFront
