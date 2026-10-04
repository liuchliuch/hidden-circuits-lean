import HiddenCircuits.Approximation.SamplerRuntime.RuntimeBounds
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! Literal bounded diagonal scan; the clock and each unary address are ordinary stacks. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Diagonal
open Complexity Complexity.OracleBlock GraphVerifier.Runtime

def check (ls hs : List BitString) (i : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => RowCheck.check ls hs i (List.replicate i true) && check ls hs (i+1) n

def state (L H clock : BitString) (i : ℕ) (flag rowflag value decisionFlag : BitString) : Store 14 := fun r =>
  if r.val=0 then L else if r.val=1 then H else if r.val=2 then clock
  else if r.val=3 then List.replicate i true else if r.val=4 then flag else if r.val=5 then rowflag
  else if r.val=6 then value else if r.val=14 then decisionFlag else []
def rowMap : Fin 12 ↪ Fin 15 where
  toFun i := ![0,1,3,6,5,7,8,9,10,11,12,13] i
  inj' := by decide +kernel
def conjunction : List Bool → Bool
  | [a,b] => a&&b
  | _ => false
noncomputable def body : OracleBlock 14 := seq (copyOn 3 6 13 (by decide) (by decide) (by decide))
  (seq (RowCheck.on rowMap) (seq (clear 6) (seq (decision 14 [4,5] conjunction)
    (seq (reverseOn 14 4 (by decide)) (push 3 true)))))
noncomputable def program : OracleBlock 14 := whilePop 2 body body

def bodyBound (ls hs : List BitString) (i : ℕ) : ℕ := RowCheck.bound ls hs i (List.replicate i true)+6*i+25

theorem body_executes (g : BitString → ℕ) (ls hs : List BitString) (clock : BitString) (i : ℕ) (flag : Bool) :
    ∃t,body.Executes g (state (encodeBitList ls) (encodeBitList hs) clock i [flag] [] [] [])
      (state (encodeBitList ls) (encodeBitList hs) clock (i+1)
        [flag&&RowCheck.check ls hs i (List.replicate i true)] [] [] []) t ∧ t≤bodyBound ls hs i := by
  let L := encodeBitList ls
  let H := encodeBitList hs
  let value := List.replicate i true
  let bit := RowCheck.check ls hs i value
  have h1 : (copyOn (3:Fin 15) 6 13 (by decide) (by decide) (by decide)).Executes g
      (state L H clock i [flag] [] [] []) (state L H clock i [flag] [] value []) (5*i+2) := by
    convert copyOn_executes g (3:Fin 15) 6 13 (by decide) (by decide) (by decide)
      (state L H clock i [flag] [] [] []) rfl using 1
    · funext r;fin_cases r <;> simp [state,value]
    · simp [state]
  obtain ⟨c,h2,hb⟩ := RowCheck.on_executes rowMap g (state L H clock i [flag] [] value []) ls hs i value
    (by funext r;fin_cases r <;> rfl)
  have e2 : Function.update (state L H clock i [flag] [] value []) (rowMap 4) [bit]=
      state L H clock i [flag] [bit] value [] := by funext r;fin_cases r <;> rfl
  change (RowCheck.on rowMap).Executes g _ (Function.update _ (rowMap 4) [bit]) c at h2
  rw [e2] at h2
  have h3 : (clear (6:Fin 15)).Executes g (state L H clock i [flag] [bit] value [])
      (state L H clock i [flag] [bit] [] []) (i+1) := by
    convert clear_executes g (6:Fin 15) _ using 1
    · funext r;fin_cases r <;> rfl
    · simp [state,value]
  have h4 : (decision (14:Fin 15) [4,5] conjunction).Executes g (state L H clock i [flag] [bit] [] [])
      (state L H clock i [] [] [] [flag&&bit]) 8 := by
    let bits : Fin 15 → Bool := fun r => if r.val=4 then flag else bit
    have hd := decision_executes (14:Fin 15) [4,5] (by decide) (by decide) conjunction bits g
      (state L H clock i [flag] [bit] [] [])
      (by intro r hr;fin_cases r <;> simp_all [state,bits])
    convert hd using 1
    funext r;fin_cases r <;> simp [state,eraseStore,conjunction,bits]
  have h5 : (reverseOn (14:Fin 15) 4 (by decide)).Executes g (state L H clock i [] [] [] [flag&&bit])
      (state L H clock i [flag&&bit] [] [] []) 3 := by
    convert reverseOn_executes g (14:Fin 15) 4 (by decide) _ using 1
    funext r;fin_cases r <;> simp [state]
  have h6 : (push (3:Fin 15) true).Executes g (state L H clock i [flag&&bit] [] [] [])
      (state L H clock (i+1) [flag&&bit] [] [] []) 1 := by
    convert push_executes g (3:Fin 15) true _ using 1
    funext r;fin_cases r <;> simp [state,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  unfold bodyBound
  dsimp [value] at hb
  omega

lemma pop_clock (L H clock : BitString) (i : ℕ) (flag : Bool) (b : Bool) :
    Function.update (state L H (b::clock) i [flag] [] [] []) 2 clock=state L H clock i [flag] [] [] [] := by
  funext r;fin_cases r <;> rfl

/-- All arrays and every raw clock have bounded termination; no promise is needed
for the physical loop. Canonical endpoints are used only in later correctness. -/
theorem program_executes (g : BitString → ℕ) (ls hs : List BitString) (clock : BitString) (i : ℕ) (flag : Bool) :
    ∃t,program.Executes g (state (encodeBitList ls) (encodeBitList hs) clock i [flag] [] [] [])
      (state (encodeBitList ls) (encodeBitList hs) [] (i+clock.length)
        [flag&&check ls hs i clock.length] [] [] []) t ∧
      t≤clock.length*(1000*((encodeBitList ls).length+(encodeBitList hs).length+i+clock.length+1)^2)+1 := by
  suffices ∃t,WhileExecution (2:Fin 15) body body g
      (state (encodeBitList ls) (encodeBitList hs) clock i [flag] [] [] [])
      (state (encodeBitList ls) (encodeBitList hs) [] (i+clock.length)
        [flag&&check ls hs i clock.length] [] [] []) t ∧
      t≤clock.length*(1000*((encodeBitList ls).length+(encodeBitList hs).length+i+clock.length+1)^2)+1 by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction clock generalizing i flag with
  | nil => exact ⟨1,by simpa [check] using (WhileExecution.empty (stack:=(2:Fin 15)) (B:=body) (C:=body)
      (g:=g) (state (encodeBitList ls) (encodeBitList hs) [] i [flag] [] [] []) rfl),by simp⟩
  | cons b clock ih =>
    obtain ⟨c,hc,hbc⟩ := body_executes g ls hs clock i flag
    obtain ⟨t,ht,hbt⟩ := ih (i+1) (flag&&RowCheck.check ls hs i (List.replicate i true))
    have h : WhileExecution (2:Fin 15) body body g
        (state (encodeBitList ls) (encodeBitList hs) (b::clock) i [flag] [] [] [])
        (state (encodeBitList ls) (encodeBitList hs) [] (i+1+clock.length)
          [(flag&&RowCheck.check ls hs i (List.replicate i true))&&check ls hs (i+1) clock.length] [] [] [])
        (1+c+1+t) := by
      cases b
      · exact WhileExecution.zero rfl (by rw [pop_clock];exact hc) ht
      · exact WhileExecution.one rfl (by rw [pop_clock];exact hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa [check,Bool.and_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    · have hr := rowCheck_bound ls hs i (List.replicate i true)
      simp only [List.length_replicate] at hr
      unfold bodyBound at hbc
      have he : (encodeBitList ls).length+(encodeBitList hs).length+(i+1)+clock.length+1=
          (encodeBitList ls).length+(encodeBitList hs).length+i+(clock.length+1)+1 := by omega
      rw [he] at hbt
      simp only [List.length_cons]
      have hpow : ((encodeBitList ls).length+(encodeBitList hs).length+i+i+1)^2≤
          4*((encodeBitList ls).length+(encodeBitList hs).length+i+(clock.length+1)+1)^2 := by nlinarith
      nlinarith

lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (RowCheck.on_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (decision_queryFree _ _ _) (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (push_queryFree _ _)))))
lemma program_queryFree : program.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.Diagonal
