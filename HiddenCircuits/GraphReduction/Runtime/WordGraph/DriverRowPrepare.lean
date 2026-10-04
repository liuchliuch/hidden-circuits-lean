import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverState
import HiddenCircuits.Complexity.UnaryArithmetic

/-! Fresh reconstruction: physical height increment and repeated-copy inner
clock construction for the98-stack graph interpolation driver. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 700000

noncomputable def rowPrepare : OracleBlock 97 :=
  seq (copyOn 2 7 19 (by decide) (by decide) (by decide))
    (seq (copyOn 7 16 19 (by decide) (by decide) (by decide))
      (seq (repeatCopy 16 3 8 19 (by decide) (by decide) (by decide)) (push 8 true)))

lemma rowPrepare_executes (g : BitString → ℕ) (w : WordInstance) (k t h : ℕ) (a : ℤ×ℤ) :
    rowPrepare.Executes g (state w k t h 0 0 a [] [] [])
      (state w k t (w.word.length+h) (2*w.particles*(w.word.length+h)+1) 0 a [] [] [])
      (5*w.word.length+(10*w.particles+9)*(w.word.length+h)+12) := by
  let H := w.word.length+h
  let s₀ := state w k t h 0 0 a [] [] []
  let s₁ := state w k t H 0 0 a [] [] []
  let s₂ := Function.update s₁ (16:Fin 98) (List.replicate H true)
  let s₃ := state w k t H (2*w.particles*H) 0 a [] [] []
  have h1 : (copyOn (2:Fin 98) 7 19 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*w.word.length+2) := by
    have hh := copyOn_executes g (2:Fin 98) 7 19 (by decide) (by decide) (by decide) s₀ rfl
    have he : Function.update s₀ (7:Fin 98) (s₀ 2++s₀ 7)=s₁ := by
      funext i;fin_cases i <;> simp [s₀,s₁,H,state,←List.replicate_add]
    rw [he] at hh
    simpa [s₀,state] using hh
  have h2 : (copyOn (7:Fin 98) 16 19 (by decide) (by decide) (by decide)).Executes g s₁ s₂ (5*H+2) := by
    simpa [s₂,s₁,state] using
      copyOn_executes g (7:Fin 98) 16 19 (by decide) (by decide) (by decide) s₁ rfl
  have h3 : (repeatCopy (16:Fin 98) 3 8 19 (by decide) (by decide) (by decide)).Executes g s₂ s₃
      ((10*w.particles+4)*H+1) := by
    have hh := unaryMultiply_executes g (16:Fin 98) 3 8 19 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s₂ H (2*w.particles)
      (by simp [s₂]) (by simp [s₂,s₁,state]) (by simp [s₂,s₁,state])
    convert hh using 1
    · funext i;fin_cases i <;> simp [s₂,s₁,s₃,state,workStore,List.replicate_add,Nat.mul_comm]
    · simp [s₂,s₁,state];ring_nf;simp
  have h4 : (push (8:Fin 98) true).Executes g s₃
      (state w k t H (2*w.particles*H+1) 0 a [] [] []) 1 := by
    have hh := push_executes g (8:Fin 98) true s₃
    have hv : s₃ 8=List.replicate (2*w.particles*H) true := rfl
    rw [hv,←List.replicate_succ] at hh
    simpa only [s₃,state_update_inner] using hh
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> dsimp only [H] <;> ring

lemma clearInnerIndex_executes (g : BitString → ℕ) (w : WordInstance) (k t h s : ℕ) (a : ℤ×ℤ) :
    (clear (9:Fin 98)).Executes g (state w k t h 0 s a [] [] [])
      (state w k t h 0 0 a [] [] []) (s+1) := by
  have hc := clear_executes g (9:Fin 98) (state w k t h 0 s a [] [] [])
  change (clear (9:Fin 98)).Executes g _
    (Function.update (state w k t h 0 s a [] [] []) 9 (List.replicate 0 true))
    ((List.replicate s true).length+1) at hc
  rw [state_update_s,List.length_replicate] at hc
  exact hc

lemma rowPrepare_queryFree : rowPrepare.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (repeatCopy_queryFree _ _ _ _ _ _ _) (push_queryFree _ _)))
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
