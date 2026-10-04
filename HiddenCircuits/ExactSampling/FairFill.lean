import HiddenCircuits.ExactSampling.FairCode

/-! A fixed two-control fair-bit loading loop. Its unary width clock is consumed
one bit at a time; every fair read is an explicit `coin` instruction. -/
namespace HiddenCircuits.ExactSampling.FairFill
open Complexity OracleBlock FairCode
variable {k : ℕ}

 def program (clock target : Fin (k+1)) : FairCode k :=
  .whilePop clock (.coin target) (.coin target)

 def state (base : Store k) (clock target : Fin (k+1)) (n : ℕ) (out : BitString) : Store k :=
  Function.update (Function.update base clock (List.replicate n true)) target out

 theorem runs (clock target : Fin (k+1)) (hne : clock≠target) (base : Store k)
    (xs out : BitString) :
    FairCode.Runs (program clock target) (state base clock target xs.length out)
      (state base clock target 0 (xs.reverse++out)) xs (3*xs.length+1) := by
  induction xs generalizing out with
  | nil =>
    simpa [state] using FairCode.Runs.loopEmpty (B:=.coin target) (C:=.coin target)
      (state base clock target 0 out) (by simp [state,hne,Ne.symm hne])
  | cons b xs ih =>
    have hp : Function.update (state base clock target (b::xs).length out) clock
        (List.replicate xs.length true)=state base clock target xs.length out := by
      funext i
      by_cases hi : i=target
      · subst i;simp [state,hne,Ne.symm hne]
      · by_cases hc : i=clock
        · subst i;simp [state,hne]
        · simp [state,hi,hc]
    have hc : FairCode.Runs (.coin target) (state base clock target xs.length out)
        (state base clock target xs.length (b::out)) [b] 1 := by
      convert FairCode.Runs.coin (state base clock target xs.length out) target b using 1
      simp [state,Function.update_idem]
    have hh := FairCode.Runs.loopTrue (q:=clock) (B:=.coin target) (C:=.coin target)
      (s:=state base clock target (b::xs).length out) (rest:=List.replicate xs.length true)
      (by simp [state,hne,Ne.symm hne,List.replicate_succ]) (by rw [hp];exact hc) (ih (b::out))
    convert hh using 1
    · simp [List.reverse_cons,List.append_assoc]
    · simp;omega

 theorem queryFree (clock target : Fin (k+1)) : (program clock target).QueryFree := ⟨trivial,trivial⟩

end HiddenCircuits.ExactSampling.FairFill
