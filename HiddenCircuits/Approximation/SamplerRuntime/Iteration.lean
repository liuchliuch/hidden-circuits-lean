import HiddenCircuits.Approximation.SamplerRuntime.StepSemantics
import HiddenCircuits.Approximation.SamplerRuntime.Output
import HiddenCircuits.Approximation.FiniteChains.CoinRealization

/-! Actual twenty-five-stack repeated sampler transitions, adapted from the surviving
partner-loop pattern and proved against the finite fair-tape experiment. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Iteration
open Complexity Complexity.OracleBlock FiniteChains GraphReduction.MonotoneEndpointEncoding
variable {n : ℕ}

def width (n : ℕ) : ℕ := 1+(Nat.size n+Nat.size n)
def iterate (E : MonotoneEndpoints n) : ℕ → E.Permutations → BitString → E.Permutations
  | 0,π,_ => π
  | t+1,π,tape => iterate E t (Step.step E π tape) (tape.drop (width n))

def state (ls hs data : BitString) (n : ℕ) (tape clock : BitString) : Store 24 := fun r =>
  if h : r.val<24 then Step.state ls hs data n tape 0 0 [] [] [] ⟨r.val,h⟩ else clock

def stepPorts : Fin 24 ↪ Fin 25 := ⟨Fin.castSucc,Fin.castSucc_injective 24⟩
noncomputable def body : OracleBlock 24 := rename Step.program stepPorts
noncomputable def program : OracleBlock 24 := whilePop 24 body body

lemma body_executes (g : BitString → ℕ) (E : MonotoneEndpoints n) (π : E.Permutations) (tape clock : BitString) :
    ∃t,body.Executes g (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (Output.witness π.val) n tape clock)
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (Output.witness (Step.step E π tape).val)
        n (tape.drop (width n)) clock) t ∧ t≤20000000*(n+1)^4 := by
  obtain ⟨t,ht,hb⟩ := Step.program_executes g E π tape
  refine ⟨t,?_,hb⟩
  apply rename_executes_to Step.program stepPorts g ht
  · funext r;simp [state,stepPorts,r.isLt,Output.witness]
  · funext r;simp [state,stepPorts,r.isLt,Output.witness,width,Step.width]
  · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 2 rfl) | exact False.elim (hr 5 rfl)

lemma pop_clock (ls hs data : BitString) (n : ℕ) (tape clock : BitString) (b : Bool) :
    Function.update (state ls hs data n tape (b::clock)) 24 clock=state ls hs data n tape clock := by
  funext r;fin_cases r <;> rfl

theorem program_executes (g : BitString → ℕ) (E : MonotoneEndpoints n) (π : E.Permutations) (tape clock : BitString) :
    ∃t,program.Executes g (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (Output.witness π.val) n tape clock)
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (Output.witness (iterate E clock.length π tape).val)
        n (tape.drop (width n*clock.length)) []) t ∧ t≤clock.length*(20000000*(n+1)^4+2)+1 := by
  suffices ∃t,WhileExecution (24:Fin 25) body body g
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (Output.witness π.val) n tape clock)
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (Output.witness (iterate E clock.length π tape).val)
        n (tape.drop (width n*clock.length)) []) t ∧ t≤clock.length*(20000000*(n+1)^4+2)+1 by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction clock generalizing π tape with
  | nil => exact ⟨1,by simpa [iterate] using (WhileExecution.empty (stack:=(24:Fin 25)) (B:=body) (C:=body) (g:=g)
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (Output.witness π.val) n tape []) rfl),by simp⟩
  | cons b clock ih =>
    obtain ⟨c,hc,hbc⟩ := body_executes g E π tape clock
    obtain ⟨t,ht,hbt⟩ := ih (Step.step E π tape) (tape.drop (width n))
    have hh : WhileExecution (24:Fin 25) body body g
        (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (Output.witness π.val) n tape (b::clock))
        (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi))
          (Output.witness (iterate E clock.length (Step.step E π tape) (tape.drop (width n))).val)
          n ((tape.drop (width n)).drop (width n*clock.length)) []) (1+c+1+t) := by
      cases b
      · exact WhileExecution.zero rfl (by rw [pop_clock];exact hc) ht
      · exact WhileExecution.one rfl (by rw [pop_clock];exact hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa [iterate,List.drop_drop,Nat.mul_succ,Nat.add_comm] using hh
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega

lemma iterate_succ_last (E : MonotoneEndpoints n) (t : ℕ) (π : E.Permutations) (tape : BitString) :
    iterate E (t+1) π tape=Step.step E (iterate E t π tape) (tape.drop (width n*t)) := by
  induction t generalizing π tape with
  | zero => rfl
  | succ t ih =>
    change iterate E (t+1) (Step.step E π tape) (tape.drop (width n))=_
    rw [ih]
    simp only [iterate,List.drop_drop,Nat.mul_succ,Nat.add_comm]

lemma iterate_append (E : MonotoneEndpoints n) (t : ℕ) (π : E.Permutations) (xs ys : BitString)
    (hx : xs.length=width n*t) : iterate E t π (xs++ys)=iterate E t π xs := by
  induction t generalizing π xs with
  | zero => rfl
  | succ t ih =>
    have hw : width n≤xs.length := by rw [hx,Nat.mul_succ];omega
    have htail : (xs.drop (width n)).length=width n*t := by rw [List.length_drop,hx,Nat.mul_succ];omega
    simp only [iterate]
    rw [Step.step_append E π xs ys hw,List.drop_append_of_le_length hw]
    exact ih _ _ htail

lemma split_ofFn (a b : ℕ) (r : CoinTape (a+b)) :
    List.ofFn r=List.ofFn ((splitTape a b r).1)++List.ofFn ((splitTape a b r).2) := by
  rw [List.ofFn_add]
  rfl

theorem iterate_ofFn (E : MonotoneEndpoints n) (t : ℕ) (π : E.Permutations) (r : CoinTape (width n*t)) :
    iterate E t π (List.ofFn r)=runCoins (MonotoneSwitch.step E (Nat.size n)) t π r := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [iterate_succ_last,runCoins]
    have he := split_ofFn (width n*t) (width n) r
    rw [he]
    rw [iterate_append E t π _ _ (by simp)]
    have hd : (List.ofFn ((splitTape (width n*t) (width n)) r).1++
        List.ofFn ((splitTape (width n*t) (width n)) r).2).drop (width n*t)=
        List.ofFn ((splitTape (width n*t) (width n)) r).2 := by
      simp
    rw [hd,ih,Step.step_ofFn]
    rfl

lemma program_queryFree : program.QueryFree := whilePop_queryFree _ _ _
  (rename_queryFree _ _ Step.program_queryFree) (rename_queryFree _ _ Step.program_queryFree)
end HiddenCircuits.Approximation.SamplerRuntime.Iteration
