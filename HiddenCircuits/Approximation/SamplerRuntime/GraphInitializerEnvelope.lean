import HiddenCircuits.Approximation.Initialization.Search.Stage.Frame
import HiddenCircuits.Approximation.Initialization.OuterLoop.Finish
import HiddenCircuits.Complexity.PolynomialBounds

/-! One explicit natural-coefficient polynomial for the fully constructed
initializer, in the pre-random sampler input-size cap. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphInitializerEnvelope
open Complexity Initialization Polynomial
noncomputable def graphP (N n L : Polynomial ℕ) : Polynomial ℕ :=
  5*N+55*(N+1)^2+4+n*n*(500*(N+n+L+1)^2+18)+40*n+30+n+L+8
noncomputable def matrixP (n b T L : Polynomial ℕ) : Polynomial ℕ :=
  5*n+2+((5*n+4)*n+1)+2+(5*T+2)+2+(n*n*(23*b+26)+T+7)+
    (n*n*(500*(n+L+1)^3+10*(L+1)+24)+40*n+30)+L+7
noncomputable def residualP (N b T : Polynomial ℕ) : Polynomial ℕ :=
  graphP N N (N*(2*N+2))+3*(2*N+1+N*N)+8+matrixP N b T (N*N*(2*b+2))+N*N+N+10
noncomputable def lengthP (N b : Polynomial ℕ) : Polynomial ℕ := 2*N+1+N*N*(2*(b+1)+2)
noncomputable def positiveP (N b T : Polynomial ℕ) : Polynomial ℕ :=
  residualP N b T+lengthP N b+2*DeterminantRuntime.timePolynomial.comp (lengthP N b)+11
noncomputable def candidateP (N B T : Polynomial ℕ) : Polynomial ℕ := positiveP N B T+14*N^2+61*N+76
noncomputable def searchP (N B T : Polynomial ℕ) : Polynomial ℕ :=
  N*(candidateP N B T+10*N+30)+20*N+30
noncomputable def stageP (N B L : Polynomial ℕ) : Polynomial ℕ :=
  searchP N B L+100000*(N+1)^4+50*(N+L+1)
noncomputable def finishP (N B L T : Polynomial ℕ) : Polynomial ℕ :=
  8*N+9+(2*N^2+2*N+3)+5*((2*N^2+3*N+T+B+L+1)+3)+5

noncomputable def naturalBound (n k T : ℕ) : ℕ := 1000*(n+k+1)^4+
  OuterLoop.loopBound (Search.Stage.timeBound n (2*n+k) (n*n*(2*n+k))) n+
  OuterLoop.Finish.timeBound n (2*n+k) (n*n*(2*n+k)) T+4
noncomputable def time : Polynomial ℕ := 1000*(X+X+1)^4+
  (X*(stageP X (2*X+X) (X*X*(2*X+X))+2*X+10)+1)+
  finishP X (2*X+X) (X*X*(2*X+X)) (3*X^4)+4

lemma stageP_eval (a b c : Polynomial ℕ) (N : ℕ) :
    (stageP a b c).eval N=Search.Stage.timeBound (a.eval N) (b.eval N) (c.eval N) := by
  simp [stageP,searchP,candidateP,positiveP,residualP,graphP,matrixP,lengthP,
    Search.Stage.timeBound,Search.Candidate.timeBound,Search.timeBound,CandidateTest.timeBound,
    ResidualPositive.timeBound,ResidualMatrixProgram.timeBound,ResidualGraphProgram.timeBound,
    MatrixInputProgram.timeBound,InducedGraphEmitter.timeBound,TutteMatrixEmitter.timeBound,ResidualPositive.matrixLength]
  omega
lemma finishP_eval (a b c d : Polynomial ℕ) (N : ℕ) :
    (finishP a b c d).eval N=OuterLoop.Finish.timeBound (a.eval N) (b.eval N) (c.eval N) (d.eval N) := by
  simp [finishP,OuterLoop.Finish.timeBound,OuterLoop.Finish.storageBound]
lemma time_eval (N : ℕ) : time.eval N=naturalBound N N (3*N^4) := by
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one,stageP_eval,finishP_eval]
  rfl

lemma stage_mono {n N b B t T : ℕ} (hn:n≤N) (hb:b≤B) (ht:t≤T) :
    Search.Stage.timeBound n b t≤Search.Stage.timeBound N B T := by
  have hlen : ResidualPositive.matrixLength n b≤ResidualPositive.matrixLength N B := by
    unfold ResidualPositive.matrixLength;gcongr
  have hd := polynomial_nat_eval_mono DeterminantRuntime.timePolynomial hlen
  dsimp only at hd
  unfold Search.Stage.timeBound Search.Candidate.timeBound Search.timeBound CandidateTest.timeBound
    ResidualPositive.timeBound ResidualMatrixProgram.timeBound ResidualGraphProgram.timeBound MatrixInputProgram.timeBound
    InducedGraphEmitter.timeBound TutteMatrixEmitter.timeBound
  gcongr

lemma naturalBound_le {n k N T : ℕ} (hn:n≤N) (hk:k≤N) (hT:T≤3*N^4) : naturalBound n k T≤time.eval N := by
  have hb : 2*n+k≤2*N+N := by omega
  have hl : n*n*(2*n+k)≤N*N*(2*N+N) := Nat.mul_le_mul (Nat.mul_le_mul hn hn) hb
  have hs := stage_mono hn hb hl
  rw [time_eval]
  unfold naturalBound OuterLoop.loopBound OuterLoop.Finish.timeBound OuterLoop.Finish.storageBound
  gcongr
end HiddenCircuits.Approximation.SamplerRuntime.GraphInitializerEnvelope
