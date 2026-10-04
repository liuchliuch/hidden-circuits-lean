import HiddenCircuits.Approximation.SelfReduction.Runtime.CountBody
import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualPolynomial

/-! A closed natural-coefficient polynomial for the complete adaptive count
loop under the concrete global unary budgets. This is derived from charged
finite instruction bounds, including each real initialized sampler call. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Polynomial

noncomputable def countBodyPolynomial (m T h : Polynomial ℕ) : Polynomial ℕ :=
  let G := 8*(X+1)^2+10*(X+1)+6
  let C := 2*G+T+1
  let M := 2*T^2
  let q := 2*h+2
  let R := 8*T
  let D := 2*q*(2*M*(X+2)+1)
  let request := 2*C+m+1
  let group := M*(22*m+33*C+46)+6*(M*(4*C+2*m+4))+
    M*(15*request+11*partnerTime.comp request+24)+5*M+12*M*(X+2)+32
  let branch := 5*D+q*(110*(M+1)*(2*X+4))+12*q*(M+1)+5*R+
    2000*(2*h+3)^2*(M+R+1)+9*M+235
  let stage := q*group+4*q*(2*M*(X+2)+1)+4+
    ((X+1)*branch+4*(X+1)*(M+1)+(X+1)*(50*(M+X+2))+2*X+16)+5*q+5*(X+1)+D+16
  5*T+13*G+stage+1000*(X+2)^2+9*M+2*X+C+50

 theorem countBodyPolynomial_eval (m T h : Polynomial ℕ) (N : ℕ) :
    (countBodyPolynomial m T h).eval N=countBodyBound N (m.eval N) (T.eval N) (h.eval N) := by
  simp only [countBodyPolynomial,countBodyBound,endpointGraphBound,endpointContextBound,
    endpointStageBound,endpointMatrixBound,samplingStageBound,sampleGroupBound,branchIterationBound,batchSize,
    eval_add,eval_mul,eval_pow,eval_comp,eval_ofNat,eval_X,eval_one]
  ring

noncomputable def countLoopPolynomial (m T h : Polynomial ℕ) : Polynomial ℕ :=
  1+X*(countBodyPolynomial m T h+2)

 theorem countLoopPolynomial_bound (m T h : Polynomial ℕ) (N d : ℕ) (hd : d ≤ N) :
    1+d*(countBodyBound N (m.eval N) (T.eval N) (h.eval N)+2) ≤ (countLoopPolynomial m T h).eval N := by
  simp only [countLoopPolynomial,eval_add,eval_mul,eval_one,eval_X,eval_ofNat,countBodyPolynomial_eval]
  gcongr

noncomputable def uniformCountTime : Polynomial ℕ :=
  countLoopPolynomial SelfReduction.EndpointResidual.uniformSampleBitsPolynomial (24*(X+1)^3) (3*X)

 theorem uniformCountTime_bound (N d : ℕ) (hd : d ≤ N) :
    1+d*(countBodyBound N (SelfReduction.EndpointResidual.uniformSampleBitsPolynomial.eval N)
      (uniformAccuracy N) (uniformConfidence N)+2) ≤ uniformCountTime.eval N := by
  have hb := countLoopPolynomial_bound SelfReduction.EndpointResidual.uniformSampleBitsPolynomial
    (24*(X+1)^3) (3*X) N d hd
  simpa [uniformAccuracy,uniformConfidence,uniformCountTime] using hb

end HiddenCircuits.Approximation.SelfReduction.Runtime
