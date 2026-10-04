import HiddenCircuits.DH.Runtime.PairCheckBody

/-! A fixed unary-clock scan of all current vertex labels. -/
namespace HiddenCircuits.DH.Runtime.PairCheck.TestRuntime
open Complexity Complexity.OracleBlock

noncomputable def loop (mode : Bool) : OracleBlock 22 := whilePop 7 (body mode) (body mode)

lemma pop_clock (n u v x : ℕ) (payload marks output clock : BitString)
    (f : Fin 11 → BitString) (b : Bool) :
    Function.update (state n u v x payload marks output (b::clock) f) 7 clock=
      state n u v x payload marks output clock f := by
  funext i;fin_cases i <;> rfl

lemma loop_execution (mode : Bool) (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (alive : Vector Bool n) (u v : Fin n) (i m : ℕ) (him : i+m≤n)
    (output au av eq edge : BitString) (a : Bool) :
    ∃t, WhileExecution (7 : Fin 23) (body mode) (body mode) g
      (state n u.val v.val i G.bits (liveBits alive) output (List.replicate m true)
        (flags [a] au av eq edge [] [] [] [] [] []))
      (state n u.val v.val (i+m) G.bits (liveBits alive) output []
        (flags [a && cellsFrom (cell mode G alive u v) i m] au av eq edge [] [] [] [] [] [])) t ∧
      t≤m*(550*(n+1)^2+2)+1 := by
  induction m generalizing i a with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [cellsFrom] using (WhileExecution.empty (stack:=(7 : Fin 23)) (B:=body mode) (C:=body mode)
      (g:=g) (state n u.val v.val i G.bits (liveBits alive) output []
        (flags [a] au av eq edge [] [] [] [] [] [])) rfl)
  | succ m ih =>
    have hi : i<n := by omega
    let x : Fin n := ⟨i,hi⟩
    obtain ⟨b,hb,hbb⟩ := body_executes mode g G alive u v x output (List.replicate m true) au av eq edge a
    obtain ⟨t,ht,htb⟩ := ih (i+1) (by omega) (a && cell mode G alive u v x)
    have hh := WhileExecution.one
      (show state n u.val v.val i G.bits (liveBits alive) output (List.replicate (m+1) true)
        (flags [a] au av eq edge [] [] [] [] [] []) 7=true::List.replicate m true from rfl)
      (by simpa only [List.replicate_succ,pop_clock] using hb) ht
    refine ⟨1+b+1+t,?_,?_⟩
    · have he : i+1+m=i+(m+1) := by omega
      simpa only [cellsFrom,dif_pos hi,he,Bool.and_assoc] using hh
    · nlinarith

lemma loop_queryFree (mode : Bool) : (loop mode).QueryFree :=
  whilePop_queryFree _ _ _ (body_queryFree mode) (body_queryFree mode)

end HiddenCircuits.DH.Runtime.PairCheck.TestRuntime
