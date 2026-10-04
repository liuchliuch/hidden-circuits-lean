import HiddenCircuits.Approximation.SamplerRuntime.PartnerMoveFrame
import HiddenCircuits.Approximation.SamplerRuntime.StepSemantics
import HiddenCircuits.Approximation.Quasimonotone.PartnerKernel

/-! A literal twenty-seven-stack lazy partner switch, reusing the verified bounded
proposal parser and preserving the PartnerIteration interface. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerStep
open Complexity Complexity.OracleBlock GraphVerifier.Runtime FiniteChains
variable {n : ℕ}

def state (graph data : BitString) (n : ℕ) (tape : BitString) (i j : ℕ) (hold : BitString) : Store 26 := fun r =>
  if r.val=0 then graph else if r.val=2 then data else if r.val=3 then List.replicate n true
  else if r.val=4 then List.replicate (Nat.size n) true else if r.val=5 then tape
  else if r.val=6 then List.replicate i true else if r.val=7 then List.replicate j true else if r.val=8 then hold else []
def prepared (graph data : BitString) (n : ℕ) (tape : BitString) (i j : ℕ) (hold : Bool) : Store 26 :=
  Function.update (Function.update (state graph data n tape i j [hold]) 9 [decide (i<n)]) 10 [decide (j<n)]
def ready (graph data : BitString) (n : ℕ) (tape : BitString) (i j : ℕ) (enabled : Bool) : Store 26 :=
  Function.update (state graph data n tape i j []) 11 [enabled]

def move (G : MatrixGraph n) (P : PerfectPartner G.graph) (i j : ℕ) (hold : Bool) : PerfectPartner G.graph :=
  if h : hold=false ∧ i<n ∧ j<n then QuasimonotoneProof.PartnerSwitch.switch G.graph ⟨i,h.2.1⟩ ⟨j,h.2.2⟩ P else P
def step (G : MatrixGraph n) (P : PerfectPartner G.graph) (tape : BitString) : PerfectPartner G.graph :=
  move G P (Step.first n tape) (Step.second n tape) (tape.headD false)

def prepareMap : Fin 24 ↪ Fin 27 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun r : Fin 27 => r.val) h)
def moveMap : Fin 20 ↪ Fin 27 where
  toFun i := ![3,0,2,6,7,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26] i
  inj' := by decide +kernel
noncomputable def prepareBlock : OracleBlock 26 := rename Step.prepare prepareMap
noncomputable def decideBlock : OracleBlock 26 := rename (decision 11 [8,9,10] Step.conjunction) prepareMap
noncomputable def moveBlock : OracleBlock 26 := PartnerMove.on moveMap
noncomputable def dispatch : OracleBlock 26 := seq decideBlock (branchPop 11 skip skip moveBlock)
noncomputable def program : OracleBlock 26 := seq prepareBlock (seq dispatch (seq (clear 6) (clear 7)))

lemma prepare_executes (g : BitString → ℕ) (graph data : BitString) (n : ℕ) (tape : BitString) :
    ∃t,prepareBlock.Executes g (state graph data n tape 0 0 [])
      (prepared graph data n (tape.drop (1+(Nat.size n+Nat.size n))) (Step.first n tape) (Step.second n tape) (tape.headD false)) t ∧
      t≤1000*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := Step.prepare_executes g graph [] data n tape
  refine ⟨t,?_,hb⟩
  apply rename_executes_to Step.prepare prepareMap g ht
  · funext r;fin_cases r <;> rfl
  · funext r;fin_cases r <;> rfl
  · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 5 rfl) | exact False.elim (hr 6 rfl) | exact False.elim (hr 7 rfl) | exact False.elim (hr 8 rfl) | exact False.elim (hr 9 rfl) | exact False.elim (hr 10 rfl)

lemma decide_executes (g : BitString → ℕ) (graph data : BitString) (n : ℕ) (tape : BitString) (i j : ℕ) (hold : Bool) :
    decideBlock.Executes g (prepared graph data n tape i j hold)
      (ready graph data n tape i j (Step.enabled hold i j n)) 10 := by
  apply rename_executes_to _ prepareMap g (Step.decide_executes g graph [] data n tape i j hold)
  · funext r;fin_cases r <;> rfl
  · funext r;fin_cases r <;> rfl
  · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 8 rfl) | exact False.elim (hr 9 rfl) | exact False.elim (hr 10 rfl) | exact False.elim (hr 11 rfl)
lemma ready_pop (graph data : BitString) (n : ℕ) (tape : BitString) (i j : ℕ) (flag : Bool) :
    Function.update (ready graph data n tape i j flag) 11 []=state graph data n tape i j [] := by
  funext r;fin_cases r <;> rfl

lemma dispatch_executes (g : BitString → ℕ) (G : MatrixGraph n) (P : PerfectPartner G.graph)
    (tape : BitString) (i j : ℕ) (hold : Bool) :
    ∃t,dispatch.Executes g (prepared G.bits (PartnerMove.witness G P) n tape i j hold)
      (state G.bits (PartnerMove.witness G (move G P i j hold)) n tape i j []) t ∧ t≤3000000*(n+1)^4+20 := by
  have hd := decide_executes g G.bits (PartnerMove.witness G P) n tape i j hold
  by_cases ha : hold=false ∧ i<n ∧ j<n
  · have he : Step.enabled hold i j n=true := by simp [Step.enabled,ha.1,ha.2.1,ha.2.2]
    rw [he] at hd
    obtain ⟨c,hc,hb⟩ := PartnerMove.on_executes moveMap g
      (state G.bits (PartnerMove.witness G P) n tape i j [])
      (state G.bits (PartnerMove.witness G (QuasimonotoneProof.PartnerSwitch.switch G.graph ⟨i,ha.2.1⟩ ⟨j,ha.2.2⟩ P)) n tape i j [])
      G P ⟨i,ha.2.1⟩ ⟨j,ha.2.2⟩
      (by funext r;fin_cases r <;> rfl) (by funext r;fin_cases r <;> rfl)
      (by intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 2 rfl))
    have hs := branchPop_true (11:Fin 27) skip skip moveBlock g
      (s:=ready G.bits (PartnerMove.witness G P) n tape i j true) rfl (by rw [ready_pop];exact hc)
    refine ⟨10+(c+2)+2,?_,by omega⟩
    simpa only [move,dif_pos ha] using seq_executes _ _ g hd hs
  · have he : Step.enabled hold i j n=false := by
      apply Bool.eq_false_iff.mpr
      simpa [Step.enabled,Bool.not_eq_true,and_assoc] using ha
    rw [he] at hd
    have hs := branchPop_false (11:Fin 27) skip skip moveBlock g
      (s:=ready G.bits (PartnerMove.witness G P) n tape i j false) rfl (by rw [ready_pop];exact skip_executes g _)
    refine ⟨15,?_,by omega⟩
    simpa only [move,dif_neg ha] using seq_executes _ _ g hd hs

theorem program_executes (g : BitString → ℕ) (G : MatrixGraph n) (P : PerfectPartner G.graph) (tape : BitString) :
    ∃t,program.Executes g (state G.bits (PartnerMove.witness G P) n tape 0 0 [])
      (state G.bits (PartnerMove.witness G (step G P tape)) n (tape.drop (1+(Nat.size n+Nat.size n))) 0 0 []) t ∧
      t≤6000000*(n+1)^4 := by
  let i := Step.first n tape
  let j := Step.second n tape
  let rest := tape.drop (Step.width n)
  let out := PartnerMove.witness G (step G P tape)
  obtain ⟨a,ha,hba⟩ := prepare_executes g G.bits (PartnerMove.witness G P) n tape
  obtain ⟨b,hb,hbb⟩ := dispatch_executes g G P rest i j (tape.headD false)
  have h6 : (clear (6:Fin 27)).Executes g (state G.bits out n rest i j []) (state G.bits out n rest 0 j []) (i+1) := by
    convert clear_executes g (6:Fin 27) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h7 : (clear (7:Fin 27)).Executes g (state G.bits out n rest 0 j []) (state G.bits out n rest 0 0 []) (j+1) := by
    convert clear_executes g (7:Fin 27) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g h6 h7)),?_⟩
  have hi : i<2^Nat.size n := Proposal.index_lt _ _
  have hj : j<2^Nat.size n := Proposal.index_lt _ _
  have hp := Step.pow_size_bound n
  have hpow : (n+1)^2≤(n+1)^4 := by nlinarith
  nlinarith

theorem step_ofFn (G : MatrixGraph n) (P : PerfectPartner G.graph) (r : CoinTape (Step.width n)) :
    step G P (List.ofFn r)=QuasimonotoneProof.PartnerSwitch.step G.graph (Nat.size n) P r := by
  unfold step
  rw [Step.first_ofFn,Step.second_ofFn,Step.hold_ofFn]
  unfold move QuasimonotoneProof.PartnerSwitch.step
  by_cases hh : (switchProposal (Nat.size n) r).1=true
  · simp [hh]
  · have hf : (switchProposal (Nat.size n) r).1=false := Bool.eq_false_iff.mpr hh
    by_cases hi : (switchProposal (Nat.size n) r).2.1.val<n
    · by_cases hj : (switchProposal (Nat.size n) r).2.2.val<n
      · simp [hf,hi,hj]
      · simp [hf,hi,hj]
    · simp [hf,hi]

lemma step_append (G : MatrixGraph n) (P : PerfectPartner G.graph) (xs ys : BitString) (h : Step.width n≤xs.length) :
    step G P (xs++ys)=step G P xs := by
  have hpos : xs≠[] := by intro hz;subst xs;simp [Step.width] at h
  have hm : Nat.size n≤xs.tail.length := by simp only [List.length_tail];unfold Step.width at h;omega
  have hm2 : Nat.size n≤(xs.tail.drop (Nat.size n)).length := by
    simp only [List.length_drop,List.length_tail];unfold Step.width at h;omega
  simp only [step,Step.first,Step.second,List.tail_append_of_ne_nil hpos]
  rw [Step.index_append _ _ _ hm,List.drop_append_of_le_length hm,Step.index_append _ _ _ hm2]
  congr 1
  cases xs with
  | nil => exact (hpos rfl).elim
  | cons b xs => rfl

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ Step.prepare_queryFree)
  (seq_queryFree _ _ (seq_queryFree _ _ (rename_queryFree _ _ (decision_queryFree _ _ _))
    (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (PartnerMove.on_queryFree _)))
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))

end HiddenCircuits.Approximation.SamplerRuntime.PartnerStep
