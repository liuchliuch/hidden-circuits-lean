import HiddenCircuits.Approximation.SamplerRuntime.StepParts
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! The complete twenty-four-stack lazy row-switch transition on arbitrary raw tapes. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Step
open Complexity Complexity.OracleBlock GraphReduction.MonotoneEndpointEncoding GraphVerifier.Runtime

variable {n : ℕ}
def move (E : MonotoneEndpoints n) (π : E.Permutations) (i j : ℕ) (hold : Bool) : E.Permutations :=
  if h : hold=false ∧ i<n ∧ j<n then E.switch ⟨i,h.2.1⟩ ⟨j,h.2.2⟩ π else π
def step (E : MonotoneEndpoints n) (π : E.Permutations) (tape : BitString) : E.Permutations :=
  move E π (first n tape) (second n tape) (tape.headD false)
def enabled (hold : Bool) (i j n : ℕ) : Bool := !hold && decide (i<n) && decide (j<n)
def conjunction : List Bool → Bool
  | [hold,a,b] => !hold && a && b
  | _ => false

def swapMap : Fin 17 ↪ Fin 24 where
  toFun i := ![0,1,2,6,7,12,13,14,15,16,17,18,19,20,21,22,23] i
  inj' := by decide +kernel
noncomputable def switchBlock : OracleBlock 23 := rename Switch.program swapMap
noncomputable def dispatch : OracleBlock 23 := seq (decision 11 [8,9,10] conjunction)
  (branchPop 11 skip skip switchBlock)
noncomputable def program : OracleBlock 23 := seq prepare (seq dispatch (seq (clear 6) (clear 7)))

def ready (L H D : BitString) (n : ℕ) (tape : BitString) (i j : ℕ) (flag : Bool) : Store 23 :=
  Function.update (state L H D n tape i j [] [] []) 11 [flag]
lemma ready_pop (L H D : BitString) (n : ℕ) (tape : BitString) (i j : ℕ) (flag : Bool) :
    Function.update (ready L H D n tape i j flag) 11 []=state L H D n tape i j [] [] [] := by
  funext r;fin_cases r <;> rfl

lemma decide_executes (g : BitString → ℕ) (L H D : BitString) (n : ℕ) (tape : BitString) (i j : ℕ) (hold : Bool) :
    (decision (11:Fin 24) [8,9,10] conjunction).Executes g
      (state L H D n tape i j [hold] [decide (i<n)] [decide (j<n)])
      (ready L H D n tape i j (enabled hold i j n)) 10 := by
  let bits : Fin 24 → Bool := fun r => if r.val=8 then hold else if r.val=9 then decide (i<n) else decide (j<n)
  have h := decision_executes (11:Fin 24) [8,9,10] (by decide) (by decide) conjunction bits g
    (state L H D n tape i j [hold] [decide (i<n)] [decide (j<n)])
    (by intro r hr;fin_cases r <;> simp_all [state,bits])
  convert h using 1
  funext r;fin_cases r <;> simp [state,ready,eraseStore,conjunction,enabled,bits]

lemma dispatch_executes (g : BitString → ℕ) (E : MonotoneEndpoints n) (π : E.Permutations)
    (tape : BitString) (i j : ℕ) (hold : Bool) :
    ∃t,dispatch.Executes g
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (encodeBitList (Switch.rowWords π.val))
        n tape i j [hold] [decide (i<n)] [decide (j<n)])
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi))
        (encodeBitList (Switch.rowWords (move E π i j hold).val)) n tape i j [] [] []) t ∧
      t≤1000000*(n+1)^4+20 := by
  let L := encodeBitList (rows E.lo)
  let H := encodeBitList (rows E.hi)
  let D := encodeBitList (Switch.rowWords π.val)
  have hd := decide_executes g L H D n tape i j hold
  by_cases ha : hold=false ∧ i<n ∧ j<n
  · have he : enabled hold i j n=true := by simp [enabled,ha.1,ha.2.1,ha.2.2]
    rw [he] at hd
    obtain ⟨c,hc,hb⟩ := Switch.program_switch g E π ⟨i,ha.2.1⟩ ⟨j,ha.2.2⟩
    have hs : switchBlock.Executes g (state L H D n tape i j [] [] [])
        (state L H (encodeBitList (Switch.rowWords (E.switch ⟨i,ha.2.1⟩ ⟨j,ha.2.2⟩ π).val)) n tape i j [] [] []) c := by
      apply rename_executes_to Switch.program swapMap g hc
      · funext r;fin_cases r <;> rfl
      · funext r;fin_cases r <;> rfl
      · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 2 rfl)
    have hbranch := branchPop_true (11:Fin 24) skip skip switchBlock g
      (s:=ready L H D n tape i j true) rfl (by rw [ready_pop];exact hs)
    refine ⟨10+(c+2)+2,?_,?_⟩
    · simpa only [move,dif_pos ha] using seq_executes _ _ g hd hbranch
    · have hp := Switch.bound_polynomial E π ⟨i,ha.2.1⟩ ⟨j,ha.2.2⟩
      omega
  · have he : enabled hold i j n=false := by
      apply Bool.eq_false_iff.mpr
      simpa [enabled,Bool.not_eq_true,and_assoc] using ha
    rw [he] at hd
    have hbranch := branchPop_false (11:Fin 24) skip skip switchBlock g
      (s:=ready L H D n tape i j false) rfl
      (by rw [ready_pop];exact skip_executes g _)
    refine ⟨15,?_,by omega⟩
    simpa only [move,dif_neg ha] using seq_executes _ _ g hd hbranch

/-- No nonempty or length premise is imposed on the random tape. Missing bits
are zero-padded; all-zero and out-of-range proposals terminate with a valid state. -/
theorem program_executes (g : BitString → ℕ) (E : MonotoneEndpoints n) (π : E.Permutations) (tape : BitString) :
    ∃t,program.Executes g
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (encodeBitList (Switch.rowWords π.val)) n tape 0 0 [] [] [])
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) (encodeBitList (Switch.rowWords (step E π tape).val))
        n (tape.drop (width n)) 0 0 [] [] []) t ∧ t≤20000000*(n+1)^4 := by
  let L := encodeBitList (rows E.lo)
  let H := encodeBitList (rows E.hi)
  let D := encodeBitList (Switch.rowWords π.val)
  let out := encodeBitList (Switch.rowWords (step E π tape).val)
  let rest := tape.drop (width n)
  let i := first n tape
  let j := second n tape
  obtain ⟨a,ha,hba⟩ := prepare_executes g L H D n tape
  obtain ⟨b,hb,hbb⟩ := dispatch_executes g E π rest i j (tape.headD false)
  have h6 : (clear (6:Fin 24)).Executes g (state L H out n rest i j [] [] [])
      (state L H out n rest 0 j [] [] []) (i+1) := by
    convert clear_executes g (6:Fin 24) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h7 : (clear (7:Fin 24)).Executes g (state L H out n rest 0 j [] [] [])
      (state L H out n rest 0 0 [] [] []) (j+1) := by
    convert clear_executes g (7:Fin 24) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g h6 h7)),?_⟩
  have hi : i<2^Nat.size n := Proposal.index_lt _ _
  have hj : j<2^Nat.size n := Proposal.index_lt _ _
  have hp := pow_size_bound n
  have hpow : (n+1)^2≤(n+1)^4 := by nlinarith
  nlinarith

lemma switchBlock_queryFree : switchBlock.QueryFree := rename_queryFree _ _ Switch.program_queryFree
lemma dispatch_queryFree : dispatch.QueryFree := seq_queryFree _ _ (decision_queryFree _ _ _)
  (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree switchBlock_queryFree)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ prepare_queryFree
  (seq_queryFree _ _ dispatch_queryFree (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))

end HiddenCircuits.Approximation.SamplerRuntime.Step
