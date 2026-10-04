import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionRounds
import HiddenCircuits.GraphReduction.UnitCoordinateExtractionCorrect
import HiddenCircuits.Complexity.UnaryPolynomial

/-! Build zero coordinates, the positive denominator, and the fixed polynomial
scan clock from the ordinary unary vertex count. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck UnitCoordinateExtraction Polynomial

def inputFrame (n : ℕ) (payload order : BitString) : Frame := ⟨n,0,payload,order,[],[],[],[]⟩
def readyFrame (n : ℕ) (payload order : BitString) : Frame := ⟨n,max 1 n,payload,order,[],[],[],[]⟩
def input (n : ℕ) (payload order : BitString) : Store 22 := state (inputFrame n payload order) [] 0 0 [] [] []

def initializeEmbedding : Fin 8 ↪ Fin 23 where
  toFun i := ![3,0,7,18,19,20,21,22] i
  inj' := by decide +kernel
noncomputable def zeros : OracleBlock 22 := DH.Runtime.WordArray.initializeOn initializeEmbedding
noncomputable def positive : OracleBlock 22 := branchPop 4 (push 4 true) (push 4 true) (push 4 true)
noncomputable def denominator : OracleBlock 22 := seq (copyOn 0 4 17 (by decide) (by decide) (by decide)) positive

def clockEmbedding : Fin 5 ↪ Fin 23 where
  toFun i := ![0,12,18,19,20] i
  inj' := by decide +kernel
noncomputable def fuelPolynomial : Polynomial ℕ := 2*(X+1)^3+1
noncomputable def clockProgram : OracleBlock 22 := rename (UnaryPolynomial.polynomialBlock fuelPolynomial) clockEmbedding
noncomputable def setup : OracleBlock 22 := seq zeros (seq denominator clockProgram)
noncomputable def initializeTime : Polynomial ℕ := UnaryPolynomial.polynomialTime fuelPolynomial+27*X+23

lemma fuelPolynomial_eval (n : ℕ) : fuelPolynomial.eval n=fuel n := by simp [fuelPolynomial,fuel]

lemma zeros_executes (g : BitString → ℕ) (n : ℕ) (payload order : BitString) :
    zeros.Executes g (input n payload order)
      (state (inputFrame n payload order) (encoded (fun _ : Fin n=>0)) 0 0 [] [] []) (22*n+8) := by
  have h := DH.Runtime.WordArray.initializeOn_executes initializeEmbedding g (input n payload order) n []
    (by funext i;fin_cases i <;> rfl)
  convert h using 1
  · funext i;fin_cases i <;> simp [input,state,inputFrame,encoded,words,List.ofFn_const,initializeEmbedding]
  · simp;omega

lemma denominator_executes (g : BitString → ℕ) (n : ℕ) (payload order values : BitString) :
    denominator.Executes g (state (inputFrame n payload order) values 0 0 [] [] [])
      (state (readyFrame n payload order) values 0 0 [] [] []) (5*n+7) := by
  let f := inputFrame n payload order
  have h1 : (copyOn (0 : Fin 23) 4 17 (by decide) (by decide) (by decide)).Executes g
      (state f values 0 0 [] [] []) (state {f with D:=n} values 0 0 [] [] []) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 23) 4 17 (by decide) (by decide) (by decide)
      (state f values 0 0 [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state,f,inputFrame]
    · simp [state,f,inputFrame]
  have h2 : positive.Executes g (state {f with D:=n} values 0 0 [] [] [])
      (state (readyFrame n payload order) values 0 0 [] [] []) 3 := by
    cases n with
    | zero =>
      apply branchPop_empty _ _ _ _ g rfl
      convert push_executes g (4 : Fin 23) true (state {f with D:=0} values 0 0 [] [] []) using 1
      funext i;fin_cases i <;> rfl
    | succ n =>
      apply branchPop_true _ _ _ _ g rfl
      convert push_executes g (4 : Fin 23) true
        (Function.update (state {f with D:=n+1} values 0 0 [] [] []) (4 : Fin 23) (List.replicate n true)) using 1
      funext i;fin_cases i <;> simp [state,readyFrame,f,inputFrame,List.replicate_succ]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma clockProgram_executes (g : BitString → ℕ) (n : ℕ) (payload order values : BitString) :
    clockProgram.Executes g (state (readyFrame n payload order) values 0 0 [] [] [])
      (state {readyFrame n payload order with clock:=List.replicate (fuel n) true} values 0 0 [] [] [])
      ((UnaryPolynomial.polynomialTime fuelPolynomial).eval n) := by
  have h := UnaryPolynomial.polynomialOn_executes clockEmbedding g fuelPolynomial n
    (state (readyFrame n payload order) values 0 0 [] [] []) (by funext i;fin_cases i <;> rfl)
  rw [fuelPolynomial_eval] at h
  convert h using 1
  funext i;fin_cases i <;> rfl

lemma initialize_executes (g : BitString → ℕ) (n : ℕ) (payload order : BitString) :
    ∃t,setup.Executes g (input n payload order)
      (state {readyFrame n payload order with clock:=List.replicate (fuel n) true}
        (encoded (fun _ : Fin n=>0)) 0 0 [] [] []) t ∧t ≤ initializeTime.eval n := by
  have h := seq_executes _ _ g (zeros_executes g n payload order)
    (seq_executes _ _ g (denominator_executes g n payload order (encoded (fun _ : Fin n=>0)))
      (clockProgram_executes g n payload order (encoded (fun _ : Fin n=>0))))
  refine ⟨_,h,?_⟩
  simp only [initializeTime,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

lemma zeros_queryFree : zeros.QueryFree := DH.Runtime.WordArray.initializeOn_queryFree _
lemma positive_queryFree : positive.QueryFree := branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _)
lemma denominator_queryFree : denominator.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) positive_queryFree
lemma clockProgram_queryFree : clockProgram.QueryFree := rename_queryFree _ _ (UnaryPolynomial.polynomialBlock_queryFree _)
lemma initialize_queryFree : setup.QueryFree := seq_queryFree _ _ zeros_queryFree (seq_queryFree _ _ denominator_queryFree clockProgram_queryFree)
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
