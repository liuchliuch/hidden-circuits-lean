import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsLoop
import HiddenCircuits.Complexity.OracleResult

/-! A clean real bit-machine step computes every coefficient of (X−a)p. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCoefficients
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

noncomputable def zeroRegisters : OracleBlock 19 :=
  seq (push 10 false) (seq (push 13 false) (seq (push 14 false) (push 15 false)))
noncomputable def prepareStep : OracleBlock 19 :=
  seq (moveOn 0 9 2 (by decide) (by decide) (by decide))
    (seq (negateOn 9) (seq (moveOn 1 16 2 (by decide) (by decide) (by decide)) zeroRegisters))

def rawStore (a cs : BitString) : Store 19 := fun i =>
  if i.val=9 then a else if i.val=16 then cs else []

theorem zeroRegisters_executes (g : BitString → ℕ) (a : ℤ) (cs : BitString) :
    zeroRegisters.Executes g (rawStore (signedBits (-a)) cs) (streamStore a 0 [] [] [] cs []) 10 := by
  let s₀ := rawStore (signedBits (-a)) cs
  let s₁ := Function.update s₀ (10:Fin 20) [false]
  let s₂ := Function.update s₁ (13:Fin 20) [false]
  let s₃ := Function.update s₂ (14:Fin 20) [false]
  let s₄ := Function.update s₃ (15:Fin 20) [false]
  have h₁ : (push (10:Fin 20) false).Executes g s₀ s₁ 1 := push_executes g _ _ s₀
  have h₂ : (push (13:Fin 20) false).Executes g s₁ s₂ 1 := push_executes g _ _ s₁
  have h₃ : (push (14:Fin 20) false).Executes g s₂ s₃ 1 := push_executes g _ _ s₂
  have h₄ : (push (15:Fin 20) false).Executes g s₃ s₄ 1 := push_executes g _ _ s₃
  have he : s₄=streamStore a 0 [] [] [] cs [] := by
    funext i;fin_cases i <;> rfl
  have h := seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄))
  rwa [he] at h

theorem prepareStep_executes (g : BitString → ℕ) (a : ℤ) (cs : BitString) :
    ∃ t, prepareStep.Executes g (binaryStore (signedBits a) cs)
      (streamStore a 0 [] [] [] cs []) t ∧ t≤6*((signedBits a).length+cs.length)+31 := by
  let s₀ : Store 19 := binaryStore (signedBits a) cs
  let s₁ := Function.update (Function.update s₀ (9:Fin 20) (signedBits a)) (0:Fin 20) []
  let s₂ := Function.update s₁ (9:Fin 20) (signedBits (-a))
  let s₃ := rawStore (signedBits (-a)) cs
  have h₁ : (moveOn (0:Fin 20) 9 2 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (6*(signedBits a).length+5) := by
    simpa [s₀,binaryStore] using moveOn_executes g (0:Fin 20) 9 2 (by decide) (by decide) (by decide) s₀ rfl
  obtain ⟨t,ht,htb⟩ := negateOn_executes g (9:Fin 20) s₁ a (by simp [s₁])
  have h₃ : (moveOn (1:Fin 20) 16 2 (by decide) (by decide) (by decide)).Executes g s₂ s₃ (6*cs.length+5) := by
    convert moveOn_executes g (1:Fin 20) 16 2 (by decide) (by decide) (by decide) s₂ rfl using 1
    funext i;fin_cases i <;> simp [s₂,s₁,s₀,s₃,binaryStore,rawStore]
  have h₄ := zeroRegisters_executes g a cs
  exact ⟨(6*(signedBits a).length+5)+(t+((6*cs.length+5)+10+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g ht (seq_executes _ _ g h₃ h₄)),by omega⟩

noncomputable def stepWork : OracleBlock 19 := seq prepareStep pass
noncomputable def stepProgram : OracleBlock 19 := seq stepWork (cleanResult 16 2 (by decide) (by decide))
noncomputable def workTime : Polynomial ℕ := X*(bodyTime+2)+17*X+4*(X+1)*(4*X+10)+50
noncomputable def stepTime : Polynomial ℕ := 25*workTime+24*X+75

def stepInputLength (a : ℤ) (cs : List ℤ) : ℕ :=
  (signedBits a).length+(encodeBitList (cs.map signedBits)).length

theorem stepWork_executes (g : BitString → ℕ) (a : ℤ) (cs : List ℤ) :
    ∃ t, stepWork.Executes g (binaryStore (signedBits a) (encodeBitList (cs.map signedBits)))
      (streamStore a (lastValue 0 cs) [] [] [] (encodeBitList ((step a cs).map signedBits)) []) t ∧
      t≤workTime.eval (stepInputLength a cs) := by
  let N := stepInputLength a cs
  have ha : (signedBits a).length≤N := by unfold N stepInputLength;omega
  have hN : 1≤N := by simp only [signedBits,List.length_cons] at ha;omega
  have hc : ∀c∈cs,(signedBits c).length≤N := by
    intro c hc
    have hh := member_length_le_encodeBitList (List.mem_map.mpr ⟨c,hc,rfl⟩ : signedBits c∈cs.map signedBits)
    unfold N stepInputLength;omega
  have hn : cs.length≤N := by
    have hh := list_length_le_encodeBitList_length (cs.map signedBits)
    simp only [List.length_map] at hh
    unfold N stepInputLength;omega
  obtain ⟨c,hc',hcb⟩ := prepareStep_executes g a (encodeBitList (cs.map signedBits))
  obtain ⟨d,hd,hdb⟩ := pass_executes g a 0 cs N ha hN hc
  refine ⟨c+d+2,seq_executes _ _ g hc' hd,?_⟩
  have hm := Nat.mul_le_mul_right (bodyTime.eval N+2) hn
  have hm' := Nat.mul_le_mul_right (4*(4*N+10)) (show cs.length+1≤N+1 by omega)
  simp only [workTime,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  change c+d+2≤N*(bodyTime.eval N+2)+17*N+4*(N+1)*(4*N+10)+50
  change c≤6*N+31 at hcb
  nlinarith

/-- Canonical signed input, canonical encoded coefficient output, and all other
tapes empty. The bound is unconditional in the actual serialized input length. -/
theorem stepProgram_executes (g : BitString → ℕ) (a : ℤ) (cs : List ℤ) :
    ∃ t, stepProgram.Executes g (binaryStore (signedBits a) (encodeBitList (cs.map signedBits)))
      (binaryStore (encodeBitList ((step a cs).map signedBits)) []) t ∧
      t≤stepTime.eval (stepInputLength a cs) := by
  obtain ⟨c,hc,hcb⟩ := stepWork_executes g a cs
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes g (16:Fin 20) 2 (by decide) (by decide) (by decide)
    (streamStore a (lastValue 0 cs) [] [] [] (encodeBitList ((step a cs).map signedBits)) [])
    (stepInputLength a cs+c) (hc.stack_bound (binaryStore_bound _ _))
  have he : Function.update (fun _ : Fin 20 => ([]:BitString)) 0
      (encodeBitList ((step a cs).map signedBits))=binaryStore (encodeBitList ((step a cs).map signedBits)) [] := by
    funext i;fin_cases i <;> rfl
  change (cleanResult (16:Fin 20) 2 (by decide) (by decide)).Executes g _
    (Function.update (fun _ : Fin 20 => ([]:BitString)) 0 (encodeBitList ((step a cs).map signedBits))) d at hd
  rw [he] at hd
  refine ⟨c+d+2,seq_executes _ _ g hc hd,?_⟩
  simp only [stepTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

theorem stepProgram_queryFree : stepProgram.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (negateOn_queryFree _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _)
          (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))))) pass_queryFree)
    (cleanResult_queryFree _ _ _ _)
end HiddenCircuits.Circuit.Runtime.SpectralCoefficients
