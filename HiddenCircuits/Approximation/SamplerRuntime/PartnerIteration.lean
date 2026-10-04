import HiddenCircuits.Approximation.SamplerRuntime.PartnerStep
import HiddenCircuits.Approximation.SamplerRuntime.CoinConcat

/-! Iterated partner transitions using the finite-tape concatenation interface. -/

/-! Iterated partner transitions using the finite-tape concatenation interface. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerIteration
open Complexity Complexity.OracleBlock FiniteChains

variable {n : ℕ}

def width (n : ℕ) : ℕ := 1+(Nat.size n+Nat.size n)

def iterate (G : MatrixGraph n) : ℕ → PerfectPartner G.graph → BitString → PerfectPartner G.graph
  | 0,P,_ => P
  | t+1,P,tape => iterate G t (PartnerStep.step G P tape) (tape.drop (width n))

def state (graph data : BitString) (n : ℕ) (tape clock : BitString) : Store 27 :=
  fun r => if h : r.val<27 then PartnerStep.state graph data n tape 0 0 [] ⟨r.val,h⟩ else clock

def stepPorts : Fin 27 ↪ Fin 28 := ⟨Fin.castSucc,Fin.castSucc_injective 27⟩
noncomputable def body : OracleBlock 27 := rename PartnerStep.program stepPorts
noncomputable def program : OracleBlock 27 := whilePop 27 body body

lemma body_executes (g : BitString → ℕ) (G : MatrixGraph n) (P : PerfectPartner G.graph)
    (tape clock : BitString) :
    ∃t,body.Executes g (state G.bits (PartnerMove.witness G P) n tape clock)
      (state G.bits (PartnerMove.witness G (PartnerStep.step G P tape)) n (tape.drop (width n)) clock) t ∧
      t≤6000000*(n+1)^4 := by
  obtain ⟨t,ht,hb⟩ := PartnerStep.program_executes g G P tape
  refine ⟨t,?_,hb⟩
  apply rename_executes_to PartnerStep.program stepPorts g ht
  · funext r;simp [state,stepPorts,r.isLt]
  · funext r;simp [state,stepPorts,r.isLt,width]
  · intro r hr;fin_cases r <;> first | rfl | exact (hr 2 rfl).elim | exact (hr 5 rfl).elim

lemma pop_clock (graph data : BitString) (n : ℕ) (tape clock : BitString) (b : Bool) :
    Function.update (state graph data n tape (b::clock)) 27 clock=state graph data n tape clock := by
  funext r;fin_cases r <;> rfl

theorem program_executes (g : BitString → ℕ) (G : MatrixGraph n) (P : PerfectPartner G.graph)
    (tape clock : BitString) :
    ∃t,program.Executes g (state G.bits (PartnerMove.witness G P) n tape clock)
      (state G.bits (PartnerMove.witness G (iterate G clock.length P tape))
        n (tape.drop (width n*clock.length)) []) t ∧
      t≤clock.length*(6000000*(n+1)^4+2)+1 := by
  suffices ∃t,WhileExecution (27:Fin 28) body body g (state G.bits (PartnerMove.witness G P) n tape clock)
      (state G.bits (PartnerMove.witness G (iterate G clock.length P tape)) n (tape.drop (width n*clock.length)) []) t ∧
      t≤clock.length*(6000000*(n+1)^4+2)+1 by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction clock generalizing P tape with
  | nil => exact ⟨1,by simpa [iterate] using (WhileExecution.empty (stack:=(27:Fin 28))
      (B:=body) (C:=body) (g:=g) (state G.bits (PartnerMove.witness G P) n tape []) rfl),by simp⟩
  | cons b clock ih =>
    obtain ⟨c,hc,hbc⟩ := body_executes g G P tape clock
    obtain ⟨t,ht,hbt⟩ := ih (PartnerStep.step G P tape) (tape.drop (width n))
    have hh : WhileExecution (27:Fin 28) body body g (state G.bits (PartnerMove.witness G P) n tape (b::clock))
        (state G.bits (PartnerMove.witness G (iterate G clock.length (PartnerStep.step G P tape) (tape.drop (width n))))
          n ((tape.drop (width n)).drop (width n*clock.length)) []) (1+c+1+t) := by
      cases b
      · exact WhileExecution.zero rfl (by rw [pop_clock];exact hc) ht
      · exact WhileExecution.one rfl (by rw [pop_clock];exact hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa [iterate,List.drop_drop,Nat.mul_succ,Nat.add_comm] using hh
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

lemma iterate_succ_last (G : MatrixGraph n) (t : ℕ) (P : PerfectPartner G.graph) (tape : BitString) :
    iterate G (t+1) P tape=PartnerStep.step G (iterate G t P tape) (tape.drop (width n*t)) := by
  induction t generalizing P tape with
  | zero => rfl
  | succ t ih =>
    change iterate G (t+1) (PartnerStep.step G P tape) (tape.drop (width n)) = _
    rw [ih]
    simp only [iterate,List.drop_drop,Nat.mul_succ,Nat.add_comm]

lemma iterate_append (G : MatrixGraph n) (t : ℕ) (P : PerfectPartner G.graph) (xs ys : BitString)
    (hx : xs.length=width n*t) : iterate G t P (xs++ys)=iterate G t P xs := by
  induction t generalizing P xs with
  | zero => rfl
  | succ t ih =>
    have hw : width n≤xs.length := by rw [hx,Nat.mul_succ];omega
    have htail : (xs.drop (width n)).length=width n*t := by rw [List.length_drop,hx,Nat.mul_succ];omega
    simp only [iterate]
    rw [PartnerStep.step_append G P xs ys hw,List.drop_append_of_le_length hw]
    exact ih _ _ htail

theorem iterate_ofFn (G : MatrixGraph n) (t : ℕ) (P : PerfectPartner G.graph)
    (r : CoinTape (width n*t)) :
    iterate G t P (List.ofFn r)=runCoins (QuasimonotoneProof.PartnerSwitch.step G.graph (Nat.size n)) t P r := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [iterate_succ_last,runCoins]
    have he := CoinLists.splitTape_ofFn (width n*t) (width n) r
    rw [he]
    rw [iterate_append G t P _ _ (by simp)]
    have hd : (List.ofFn ((splitTape (width n*t) (width n)) r).1++
        List.ofFn ((splitTape (width n*t) (width n)) r).2).drop (width n*t)=
        List.ofFn ((splitTape (width n*t) (width n)) r).2 := by
      rw [←he]
      exact CoinLists.splitTape_drop _ _ r
    rw [hd,ih,PartnerStep.step_ofFn]
    rfl

lemma program_queryFree : program.QueryFree := whilePop_queryFree _ _ _
  (rename_queryFree _ _ PartnerStep.program_queryFree) (rename_queryFree _ _ PartnerStep.program_queryFree)

end HiddenCircuits.Approximation.SamplerRuntime.PartnerIteration
