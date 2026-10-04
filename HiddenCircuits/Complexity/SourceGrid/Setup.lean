import HiddenCircuits.Complexity.SourceGrid.Ports
import HiddenCircuits.Complexity.GridDenominatorRuntime
import HiddenCircuits.Complexity.CNFCloneEmitter.Dimensions

/-! Actual canonical source preprocessing: preserve formula bytes, parse its
unary dimensions, generate the common denominator, and initialize zero sum. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock BinaryArithmetic Polynomial

def baseStore (n m : ℕ) (formula denominator accumulator payload : BitString) : Store 42 := fun q =>
  if q.val=0 then List.replicate n true else if q.val=1 then List.replicate m true else
  if q.val=9 then formula else if q.val=10 then denominator else if q.val=11 then accumulator else
  if q.val=17 then payload else []

def dimensionsEmbedding : Fin 8 ↪ Fin 43 where
  toFun q := if q.val=0 then 9 else if q.val=1 then 17 else if q.val=2 then 18 else
    if q.val=3 then 0 else if q.val=4 then 19 else if q.val=5 then 20 else if q.val=6 then 1 else 21
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def denominatorEmbedding : Fin 22 ↪ Fin 43 where
  toFun q := if q.val=0 then 0 else if q.val=1 then 1 else if q.val=2 then 10 else ⟨q.val+14,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def setup : OracleBlock 42 :=
  seq (moveOn 0 9 17 (by decide) (by decide) (by decide))
    (seq (rename CNFCloneEmitter.dimensionsBlock dimensionsEmbedding)
      (seq (clear 17) (seq (GridDenominatorRuntime.programOn denominatorEmbedding) (push 11 false))))
noncomputable def setupTime : Polynomial ℕ := GridDenominatorRuntime.time.comp (2*X)+37*X+45

theorem setup_executes (g : BitString → ℕ) (F : CNFInput) :
    ∃ c, setup.Executes g (Function.update (fun _ => []) 0 (CNFInput.encode F))
      (GridRuntime.initialStore F.1 F.2.1 (frame {formula:=CNFInput.encode F,denominator:=signedBits (gridDenominator F.1 F.2.1),accumulator:=signedBits 0})) c ∧
      c≤setupTime.eval (CNFInput.encode F).length := by
  let bits := CNFInput.encode F
  let payload := encodeBitList ((List.ofFn F.2.2.clause).map CNF.clauseBits)
  let s₀ := baseStore 0 0 bits [] [] []
  let s₁ := baseStore F.1 F.2.1 bits [] [] payload
  let s₂ := baseStore F.1 F.2.1 bits [] [] []
  let s₃ := baseStore F.1 F.2.1 bits (signedBits (gridDenominator F.1 F.2.1)) [] []
  let s₄ := baseStore F.1 F.2.1 bits (signedBits (gridDenominator F.1 F.2.1)) (signedBits 0) []
  have h₀ : (moveOn (0 : Fin 43) 9 17 (by decide) (by decide) (by decide)).Executes g
      (Function.update (fun _ => []) 0 bits) s₀ (6*bits.length+5) := by
    convert moveOn_executes g (0 : Fin 43) 9 17 (by decide) (by decide) (by decide)
      (Function.update (fun _ => []) 0 bits) rfl using 1
    funext q;fin_cases q <;> simp [s₀,baseStore]
  obtain ⟨d,hd,hdb⟩ := CNFCloneEmitter.dimensions_cnf g F.2.2
  change d≤30*bits.length+30 at hdb
  have h₁ : (rename CNFCloneEmitter.dimensionsBlock dimensionsEmbedding).Executes g s₀ s₁ d := by
    apply rename_executes_to _ dimensionsEmbedding g hd
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq;fin_cases q <;> first | rfl | (exfalso;exact hq 1 rfl) | (exfalso;exact hq 3 rfl) | (exfalso;exact hq 6 rfl)
  have h₂ : (clear (17 : Fin 43)).Executes g s₁ s₂ (payload.length+1) := by
    convert clear_executes g (17 : Fin 43) s₁ using 1
    funext q;fin_cases q <;> rfl
  obtain ⟨e,he,heb⟩ := GridDenominatorRuntime.programOn_executes denominatorEmbedding g s₂ F.1 F.2.1
    (by funext q;fin_cases q <;> rfl)
  have h₃ : (GridDenominatorRuntime.programOn denominatorEmbedding).Executes g s₂ s₃ e := by
    convert he using 1
    funext q;fin_cases q <;> rfl
  have h₄ : (push (11 : Fin 43) false).Executes g s₃ s₄ 1 := by
    convert push_executes g (11 : Fin 43) false s₃ using 1
    funext q;fin_cases q <;> rfl
  have hout : s₄=GridRuntime.initialStore F.1 F.2.1 (frame {formula:=CNFInput.encode F,denominator:=signedBits (gridDenominator F.1 F.2.1),accumulator:=signedBits 0}) := by
    funext q;fin_cases q <;> rfl
  have h := seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)))
  rw [hout] at h
  refine ⟨_,h,?_⟩
  have hlen := CNFInput.encode_length_lower F
  have hde := polynomial_nat_eval_mono GridDenominatorRuntime.time
    (show F.1+F.2.1≤2*bits.length by dsimp [bits];omega)
  dsimp only at hde
  have hp : payload.length≤bits.length := by
    change payload.length≤F.2.2.bits.length
    simp only [CNF.bits,pairBits_length,List.length_replicate]
    dsimp [payload]
    omega
  simp only [setupTime,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X]
  dsimp only [bits] at *
  omega

lemma setup_queryFree : setup.QueryFree := seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ CNFCloneEmitter.dimensions_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _
      (GridDenominatorRuntime.programOn_queryFree _) (push_queryFree _ _))))

end HiddenCircuits.Complexity.SourceGrid
