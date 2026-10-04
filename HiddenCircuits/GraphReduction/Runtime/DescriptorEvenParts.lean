import HiddenCircuits.GraphReduction.Runtime.DescriptorFrontParts

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorEven
open Complexity OracleBlock BinaryArithmetic DescriptorFront
set_option maxHeartbeats 800000

def vertex (layer : ℕ) : VertexRecord := ⟨false,false,layer,0,backgroundCode⟩
noncomputable def sourceRow : OracleBlock 19 := seq (copyOn 12 9 6 (by decide) (by decide) (by decide)) maskRow
noncomputable def differenceRow (target : Bool) : OracleBlock 19 :=
  seq (if target then copyOn 8 14 6 (by decide) (by decide) (by decide) else copyOn 12 14 6 (by decide) (by decide) (by decide))
    (seq (copyOn 13 15 6 (by decide) (by decide) (by decide)) (seq difference maskRow))

lemma sourceRow_executes (g : BitString → ℕ) (v : VertexRecord) (hv : v.track=0) (width height samples clock : ℕ)
    (S T pairs out : BitString) (count : ℕ) :
    ∃c,sourceRow.Executes g (workState v width height samples clock [] S T pairs out count)
      (workState v width height samples clock [] S T pairs
        ((encodeBitList ((DescriptorMaskRow.records v S).map encodeVertex)).reverse++out) (count+(DescriptorMaskRow.records v S).length)) c ∧
      c≤S.length*(20*v.layer+20*S.length+14*v.cut.index+125)+8 := by
  have hp : (copyOn (12:Fin 20) 9 6 (by decide) (by decide) (by decide)).Executes g
      (workState v width height samples clock [] S T pairs out count)
      (workState v width height samples clock S S T pairs out count) (5*S.length+2) := by
    convert copyOn_executes g (12:Fin 20) 9 6 (by decide) (by decide) (by decide)
      (workState v width height samples clock [] S T pairs out count) rfl using 1
    funext i;fin_cases i <;> simp [workState,DescriptorAtom.state]
  obtain ⟨c,hc,hb⟩ := maskRow_executes g v hv width height samples clock S S T pairs out count
  exact ⟨_,seq_executes _ _ g hp hc,by nlinarith⟩

lemma differenceRow_executes (g : BitString → ℕ) (target : Bool) (v : VertexRecord) (hv : v.track=0)
    (width height samples clock : ℕ) (S T pairs out : BitString) (count : ℕ)
    (hlen : (if target then List.replicate width true else S).length=T.length) :
    let xs := if target then List.replicate width true else S
    let mask := DescriptorMaskDifference.difference xs T
    ∃c,(differenceRow target).Executes g (workState v width height samples clock [] S T pairs out count)
      (workState v width height samples clock [] S T pairs
        ((encodeBitList ((DescriptorMaskRow.records v mask).map encodeVertex)).reverse++out)
        (count+(DescriptorMaskRow.records v mask).length)) c ∧
      c≤xs.length*(20*v.layer+20*xs.length+14*v.cut.index+137)+18 := by
  let xs := if target then List.replicate width true else S
  let mask := DescriptorMaskDifference.difference xs T
  let start := workState v width height samples clock [] S T pairs out count
  let a := Function.update start (14:Fin 20) xs
  let b := Function.update a (15:Fin 20) T
  have h₁ : (if target then copyOn (8:Fin 20) 14 6 (by decide) (by decide) (by decide) else copyOn 12 14 6 (by decide) (by decide) (by decide)).Executes g
      start a (5*xs.length+2) := by
    cases target
    · simpa [a,start,xs,workState] using copyOn_executes g (12:Fin 20) 14 6 (by decide) (by decide) (by decide) start rfl
    · simpa [a,start,xs,workState] using copyOn_executes g (8:Fin 20) 14 6 (by decide) (by decide) (by decide) start rfl
  have h₂ : (copyOn (13:Fin 20) 15 6 (by decide) (by decide) (by decide)).Executes g a b (5*T.length+2) := by
    simpa [b,a,start,workState] using copyOn_executes g (13:Fin 20) 15 6 (by decide) (by decide) (by decide) a rfl
  have h₃ := difference_executes g v width height samples clock S T pairs out xs T count hlen
  obtain ⟨c,h₄,hb⟩ := maskRow_executes g v hv width height samples clock mask S T pairs out count
  have hm : mask.length=xs.length := DescriptorMaskDifference.difference_length xs T hlen
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  change _≤xs.length*(20*v.layer+20*xs.length+14*v.cut.index+137)+18
  rw [hm] at hb
  change xs.length=T.length at hlen
  nlinarith

lemma increment_layer (g : BitString → ℕ) (v : VertexRecord) (width height samples clock : ℕ)
    (S T pairs out : BitString) (count : ℕ) :
    (push (1:Fin 20) true).Executes g (workState v width height samples clock [] S T pairs out count)
      (workState {v with layer:=v.layer+1} width height samples clock [] S T pairs out count) 1 := by
  convert push_executes g (1:Fin 20) true (workState v width height samples clock [] S T pairs out count) using 1
  funext i;fin_cases i <;> simp [workState,DescriptorAtom.state,DescriptorAtom.tagBits,List.replicate_succ]

lemma clear_layer (g : BitString → ℕ) (v : VertexRecord) (width height samples clock : ℕ)
    (S T pairs out : BitString) (count : ℕ) :
    (clear (1:Fin 20)).Executes g (workState v width height samples clock [] S T pairs out count)
      (workState {v with layer:=0} width height samples clock [] S T pairs out count) (v.layer+1) := by
  convert clear_executes g (1:Fin 20) (workState v width height samples clock [] S T pairs out count) using 1
  · funext i;fin_cases i <;> rfl
  · simp [workState,DescriptorAtom.state]
end HiddenCircuits.GraphReduction.Runtime.DescriptorEven
