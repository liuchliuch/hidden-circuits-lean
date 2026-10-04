import HiddenCircuits.Approximation.SamplerRuntime.Initialize
import HiddenCircuits.Approximation.SamplerRuntime.Iteration
import HiddenCircuits.Approximation.SamplerRuntime.ProposalWidth
import HiddenCircuits.Approximation.SamplerRuntime.Budget

/-! Physical twenty-seven-stack composition preserving the Core interface. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Core
open Complexity Complexity.OracleBlock GraphReduction.MonotoneEndpointEncoding
abbrev unary (n : ℕ) : BitString := List.replicate n true

def state (ls hs : BitString) (n N : ℕ) (tape out width clock flag : BitString) : Store 26 := fun r =>
  if r.val=0 then ls else if r.val=1 then hs else if r.val=2 then out else if r.val=3 then unary n
  else if r.val=4 then width else if r.val=5 then tape else if r.val=24 then clock
  else if r.val=25 then unary N else if r.val=26 then flag else []
def initializeMap : Fin 18 ↪ Fin 27 where
  toFun i := ![0,1,2,3,6,7,26,8,9,10,11,12,13,14,15,16,17,18] i
  inj' := by decide +kernel
def widthMap : Fin 6 ↪ Fin 27 where
  toFun i := ![3,6,4,7,8,9] i
  inj' := by decide +kernel
def clockMap : Fin 5 ↪ Fin 27 where
  toFun i := ![25,24,6,7,8] i
  inj' := by decide +kernel
def iterationMap : Fin 25 ↪ Fin 27 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun r : Fin 27 => r.val) h)
noncomputable def initializeBlock : OracleBlock 26 := rename Initialize.program initializeMap
noncomputable def widthBlock : OracleBlock 26 := ProposalWidth.on widthMap
noncomputable def clockBlock : OracleBlock 26 := rename (UnaryPolynomial.polynomialBlock Budget.stepsPolynomial) clockMap
noncomputable def iterationBlock : OracleBlock 26 := rename Iteration.program iterationMap
noncomputable def success : OracleBlock 26 := seq widthBlock (seq clockBlock (seq iterationBlock (push 2 true)))
noncomputable def program : OracleBlock 26 := seq initializeBlock (branchPop 26 (clear 2) (clear 2) success)

theorem initialize_executes (g : BitString → ℕ) (ls hs : List BitString) (n N : ℕ) (tape : BitString) :
    ∃t,initializeBlock.Executes g (state (encodeBitList ls) (encodeBitList hs) n N tape [] [] [] [])
      (state (encodeBitList ls) (encodeBitList hs) n N tape (Identity.evaluate (unary n)) [] [] [Diagonal.check ls hs 0 n]) t ∧
      t≤2000*((encodeBitList ls).length+(encodeBitList hs).length+n+1)^3 := by
  obtain ⟨t,ht,hb⟩ := Initialize.program_executes g ls hs n
  refine ⟨t,?_,hb⟩
  apply rename_executes_to Initialize.program initializeMap g ht
  · funext r;fin_cases r <;> rfl
  · funext r;fin_cases r <;> rfl
  · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 2 rfl) | exact False.elim (hr 6 rfl)

lemma width_executes (g : BitString → ℕ) (L H : BitString) (n N : ℕ) (tape out : BitString) :
    ∃t,widthBlock.Executes g (state L H n N tape out [] [] [])
      (state L H n N tape out (unary (Nat.size n)) [] []) t ∧ t≤40*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := ProposalWidth.on_executes widthMap g (state L H n N tape out [] [] []) (unary n)
    (by funext r;fin_cases r <;> rfl)
  refine ⟨t,?_,by simpa using hb⟩
  convert ht using 1
  funext r;fin_cases r <;> simp [state,widthMap]

lemma clock_executes (g : BitString → ℕ) (L H : BitString) (n N : ℕ) (tape out : BitString) :
    clockBlock.Executes g (state L H n N tape out (unary (Nat.size n)) [] [])
      (state L H n N tape out (unary (Nat.size n)) (unary (Budget.steps N)) [])
      ((UnaryPolynomial.polynomialTime Budget.stepsPolynomial).eval N) := by
  have h := UnaryPolynomial.polynomialOn_executes clockMap g Budget.stepsPolynomial N
    (state L H n N tape out (unary (Nat.size n)) [] []) (by funext r;fin_cases r <;> rfl)
  rw [Budget.steps_eval] at h
  convert h using 1
  funext r;fin_cases r <;> rfl

variable {n : ℕ}
lemma iteration_executes (g : BitString → ℕ) (E : MonotoneEndpoints n) (N : ℕ) (π : E.Permutations) (tape : BitString) :
    ∃t,iterationBlock.Executes g
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) n N tape (Output.witness π.val)
        (unary (Nat.size n)) (unary (Budget.steps N)) [])
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) n N
        (tape.drop (Iteration.width n*Budget.steps N)) (Output.witness (Iteration.iterate E (Budget.steps N) π tape).val)
        (unary (Nat.size n)) [] []) t ∧ t≤Budget.steps N*(20000000*(n+1)^4+2)+1 := by
  obtain ⟨t,ht,hb⟩ := Iteration.program_executes g E π tape (unary (Budget.steps N))
  refine ⟨t,?_,by simpa using hb⟩
  apply rename_executes_to Iteration.program iterationMap g ht
  · funext r;fin_cases r <;> rfl
  · funext r;fin_cases r <;> simp [state,iterationMap,Iteration.state,Step.state]
  · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 2 rfl) | exact False.elim (hr 5 rfl) | exact False.elim (hr 24 rfl)

theorem success_executes (g : BitString → ℕ) (E : MonotoneEndpoints n) (N : ℕ) (π : E.Permutations) (tape : BitString) :
    ∃t,success.Executes g
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) n N tape (Output.witness π.val) [] [] [])
      (state (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi)) n N
        (tape.drop (Iteration.width n*Budget.steps N)) (Output.success (Iteration.iterate E (Budget.steps N) π tape).val)
        (unary (Nat.size n)) [] []) t ∧
      t≤(UnaryPolynomial.polynomialTime Budget.stepsPolynomial).eval N+
        Budget.steps N*(20000000*(n+1)^4+2)+40*(n+1)^2+8 := by
  let L := encodeBitList (rows E.lo)
  let H := encodeBitList (rows E.hi)
  obtain ⟨a,ha,hba⟩ := width_executes g L H n N tape (Output.witness π.val)
  have hb := clock_executes g L H n N tape (Output.witness π.val)
  obtain ⟨c,hc,hbc⟩ := iteration_executes g E N π tape
  have hd : (push (2:Fin 27) true).Executes g
      (state L H n N (tape.drop (Iteration.width n*Budget.steps N))
        (Output.witness (Iteration.iterate E (Budget.steps N) π tape).val) (unary (Nat.size n)) [] [])
      (state L H n N (tape.drop (Iteration.width n*Budget.steps N))
        (Output.success (Iteration.iterate E (Budget.steps N) π tape).val) (unary (Nat.size n)) [] []) 1 := by
    convert push_executes g (2:Fin 27) true _ using 1
    funext r;fin_cases r <;> rfl
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),by omega⟩

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ Initialize.program_queryFree)
  (branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _)
    (seq_queryFree _ _ (ProposalWidth.on_queryFree _) (seq_queryFree _ _
      (rename_queryFree _ _ (UnaryPolynomial.polynomialBlock_queryFree _))
      (seq_queryFree _ _ (rename_queryFree _ _ Iteration.program_queryFree) (push_queryFree _ _)))))

end HiddenCircuits.Approximation.SamplerRuntime.Core
