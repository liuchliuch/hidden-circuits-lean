import HiddenCircuits.Complexity.GridTermAlgebra
import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine

/-! Actual per-query shared-denominator interpolation accumulation. Five fixed
integer assignments are compiled to the proved binary arithmetic programs. -/
namespace HiddenCircuits.Complexity.GridTermRuntime
open OracleBlock BinaryArithmetic BinaryArithmetic.RegisterMachine

def registers (D di dj nu value acc temp : ℤ) : Fin 7 → ℤ := fun i =>
  if i.val=0 then D else if i.val=1 then di else if i.val=2 then dj else
  if i.val=3 then nu else if i.val=4 then value else if i.val=5 then acc else temp

def code : List Instruction :=
  [⟨.multiply,6,1,2⟩,⟨.divide,6,0,6⟩,⟨.multiply,6,6,3⟩,
   ⟨.multiply,6,6,4⟩,⟨.add,5,5,6⟩]

noncomputable def program : OracleBlock 15 := compile code
noncomputable def time : Polynomial ℕ := straightTime code

def term (D di dj nu value : ℤ) : ℤ := (D/(di*dj))*nu*value

lemma evaluate_code (D di dj nu value acc temp : ℤ) :
    evaluate code (registers D di dj nu value acc temp) =
      registers D di dj nu value (acc+term D di dj nu value) (term D di dj nu value) := by
  funext i
  fin_cases i <;> simp [code,evaluate,Instruction.eval,Operation.eval,registers,term]

lemma valid_code (D di dj nu value acc temp : ℤ) (hn : di*dj≠0) (hd : di*dj∣D) :
    Valid code (registers D di dj nu value acc temp) := by
  simp [code,Valid,Instruction.eval,Operation.Valid,Operation.eval,registers,hn,hd]

lemma registers_bounded (D di dj nu value acc temp : ℤ) (B : ℕ)
    (hD : (signedBits D).length≤B) (hi : (signedBits di).length≤B)
    (hj : (signedBits dj).length≤B) (hn : (signedBits nu).length≤B)
    (hv : (signedBits value).length≤B) (ha : (signedBits acc).length≤B)
    (ht : (signedBits temp).length≤B) : Bounded B (registers D di dj nu value acc temp) := by
  intro i;fin_cases i <;> simp only [registers,ite_true,ite_false] <;> assumption

/-- A direct actual execution theorem with only input-length and mathematical
exact-divisibility hypotheses. All five arithmetic calls and their work tapes
are physically executed; no intermediate-bit or runtime assumption remains. -/
theorem program_executes (g : BitString → ℕ) (D di dj nu value acc temp : ℤ) (B : ℕ)
    (hn : di*dj≠0) (hd : di*dj∣D) (hb : Bounded B (registers D di dj nu value acc temp)) :
    ∃ cost, program.Executes g (store [] [] (signedBits ∘ registers D di dj nu value acc temp))
      (store [] [] (signedBits ∘ registers D di dj nu value
        (acc+term D di dj nu value) (term D di dj nu value))) cost ∧ cost≤time.eval B := by
  simpa only [evaluate_code] using compile_polynomial code g (registers D di dj nu value acc temp) B hb
    (valid_code D di dj nu value acc temp hn hd)

def inputLength (D di dj nu value acc temp : ℤ) : ℕ :=
  (signedBits D).length+(signedBits di).length+(signedBits dj).length+(signedBits nu).length+
  (signedBits value).length+(signedBits acc).length+(signedBits temp).length

/-- Unconditional polynomial in the complete physical signed-register input. -/
theorem program_polynomial (g : BitString → ℕ) (D di dj nu value acc temp : ℤ)
    (hn : di*dj≠0) (hd : di*dj∣D) :
    ∃ cost, program.Executes g (store [] [] (signedBits ∘ registers D di dj nu value acc temp))
      (store [] [] (signedBits ∘ registers D di dj nu value
        (acc+term D di dj nu value) (term D di dj nu value))) cost ∧
      cost≤time.eval (inputLength D di dj nu value acc temp) := by
  apply program_executes g D di dj nu value acc temp _ hn hd
  apply registers_bounded <;> unfold inputLength <;> omega

/-- Specialization to the actual interpolation weights discharges every
nonzero/exact-division condition from the algebraic source reduction. -/
theorem grid_executes (g : BitString → ℕ) (dx dy : ℕ) (i : Fin (dx+1)) (j : Fin (dy+1))
    (value acc temp : ℤ) (B : ℕ)
    (hb : Bounded B (registers (gridDenominator dx dy) (interpolationDenominator dx i)
      (interpolationDenominator dy j) (interpolationNegativeNumerator dy j) value acc temp)) :
    ∃ cost, program.Executes g
      (store [] [] (signedBits ∘ registers (gridDenominator dx dy) (interpolationDenominator dx i)
        (interpolationDenominator dy j) (interpolationNegativeNumerator dy j) value acc temp))
      (store [] [] (signedBits ∘ registers (gridDenominator dx dy) (interpolationDenominator dx i)
        (interpolationDenominator dy j) (interpolationNegativeNumerator dy j) value
        (acc+gridTerm dx dy i j value) (gridTerm dx dy i j value))) cost ∧ cost≤time.eval B := by
  exact program_executes g _ _ _ _ value acc temp B (gridDivisor_ne_zero dx dy i j) (gridDivisor_dvd dx dy i j) hb

lemma program_queryFree : program.QueryFree := compile_queryFree code

lemma term_length (D di dj nu value acc temp : ℤ) (B : ℕ) (hn : di*dj≠0) (hd : di*dj∣D)
    (hb : Bounded B (registers D di dj nu value acc temp)) :
    (signedBits (term D di dj nu value)).length≤32*(B+3) := by
  have h := (safe_of_bounded code (registers D di dj nu value acc temp) B hb
    (valid_code D di dj nu value acc temp hn hd)).final 6
  simpa only [evaluate_code,registers,code,List.length_cons,List.length_nil,ite_false] using h

noncomputable def programOn {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (D di dj nu value acc temp : ℤ) (B : ℕ)
    (hn : di*dj≠0) (hd : di*dj∣D) (hb : Bounded B (registers D di dj nu value acc temp))
    (hs : s∘φ=store [] [] (signedBits ∘ registers D di dj nu value acc temp)) :
    ∃ c, (programOn φ).Executes g s
      (Function.update (Function.update s (φ 14) (signedBits (acc+term D di dj nu value)))
        (φ 15) (signedBits (term D di dj nu value))) c ∧ c≤time.eval B := by
  obtain ⟨c,hc,hcb⟩ := program_executes g D di dj nu value acc temp B hn hd hb
  refine ⟨c,?_,hcb⟩
  apply rename_executes_to program φ g hc hs
  · funext q
    have hq := congrFun hs q
    change s (φ q)=_ at hq
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hq]
    fin_cases q <;> rfl
  · intro q hq
    simp only [Function.update_of_ne (hq 14).symm,Function.update_of_ne (hq 15).symm]

lemma programOn_queryFree {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Complexity.GridTermRuntime
