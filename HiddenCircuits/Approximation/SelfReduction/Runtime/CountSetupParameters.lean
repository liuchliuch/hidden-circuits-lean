import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualPolynomial
import HiddenCircuits.Complexity.UnaryPolynomial

/-! Fixed, query-free unary generation of all global counting parameters. The
argument is the length of the request before random bits are attached. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
open Complexity OracleBlock Polynomial
set_option maxHeartbeats 1000000

noncomputable def parameterPolynomial (i : Fin 8) : Polynomial ℕ :=
  ![SelfReduction.EndpointResidual.uniformSampleBitsPolynomial,
    2*(24*(X+1)^3)^2,8*(24*(X+1)^3),X+1,6*X+2,24*(X+1)^3,
    SelfReduction.EndpointResidual.randomBitsPolynomial,3*X] i

/-- Port zero is N; ports1--8 contain the computed prefix;9--11 are scratch. -/
noncomputable def parameterState (N j : ℕ) : Store 11 := fun i =>
  if i.val=0 then List.replicate N true else
  if h : 1 ≤ i.val ∧ i.val ≤ 8 ∧ i.val ≤ j then
    List.replicate ((parameterPolynomial ⟨i.val-1,by omega⟩).eval N) true else []

def parameterPorts (q : Fin 8) : Fin 5 ↪ Fin 12 where
  toFun i := if i.val=0 then 0 else if i.val=1 then ⟨q.val+1,by omega⟩
    else if i.val=2 then 9 else if i.val=3 then 10 else 11
  inj' := by fin_cases q <;> decide +kernel
noncomputable def parameterStep (q : Fin 8) : OracleBlock 11 :=
  rename (UnaryPolynomial.polynomialBlock (parameterPolynomial q)) (parameterPorts q)

lemma parameterStep_executes (g : BitString → ℕ) (N : ℕ) (q : Fin 8) :
    (parameterStep q).Executes g (parameterState N q.val) (parameterState N (q.val+1))
      ((UnaryPolynomial.polynomialTime (parameterPolynomial q)).eval N) := by
  have h := UnaryPolynomial.polynomialOn_executes (parameterPorts q) g (parameterPolynomial q) N
    (parameterState N q.val) (by
      funext i
      fin_cases i <;> simp [parameterPorts,parameterState,UnaryPolynomial.state]
      )
  convert h using 1
  funext i
  fin_cases q <;> fin_cases i <;> simp [parameterState,parameterPorts,parameterPolynomial]

noncomputable def parameterPrefix : (j : ℕ) → j≤8 → OracleBlock 11
  | 0,_ => skip
  | j+1,h => seq (parameterPrefix j (by omega)) (parameterStep ⟨j,by omega⟩)
noncomputable def parameterPrefixTime : (j : ℕ) → j≤8 → Polynomial ℕ
  | 0,_ => 1
  | j+1,h => parameterPrefixTime j (by omega)+
      UnaryPolynomial.polynomialTime (parameterPolynomial ⟨j,by omega⟩)+2

lemma parameterPrefix_executes (g : BitString → ℕ) (N j : ℕ) (hj : j≤8) :
    (parameterPrefix j hj).Executes g (parameterState N 0) (parameterState N j)
      ((parameterPrefixTime j hj).eval N) := by
  induction j with
  | zero => simpa [parameterPrefix,parameterPrefixTime] using skip_executes g (parameterState N 0)
  | succ j ih =>
    simpa [parameterPrefix,parameterPrefixTime] using seq_executes _ _ g (ih (by omega))
      (parameterStep_executes g N ⟨j,by omega⟩)
lemma parameterPrefix_queryFree (j : ℕ) (hj : j≤8) : (parameterPrefix j hj).QueryFree := by
  induction j with
  | zero => exact skip_queryFree
  | succ j ih =>
    exact seq_queryFree _ _ (ih (by omega))
      (rename_queryFree _ _ (UnaryPolynomial.polynomialBlock_queryFree _))
noncomputable def parameters : OracleBlock 11 := parameterPrefix 8 (by omega)
noncomputable def parametersTime : Polynomial ℕ := parameterPrefixTime 8 (by omega)
lemma parameters_executes (g : BitString → ℕ) (N : ℕ) :
    parameters.Executes g (parameterState N 0) (parameterState N 8) (parametersTime.eval N) :=
  parameterPrefix_executes g N 8 (by omega)
lemma parameters_queryFree : parameters.QueryFree := parameterPrefix_queryFree 8 (by omega)
end HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetup
