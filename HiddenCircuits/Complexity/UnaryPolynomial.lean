import HiddenCircuits.Complexity.UnaryArithmetic
import Mathlib.Algebra.Polynomial.Inductions

/-! Uniform, actual finite-bit evaluation of any fixed natural-coefficient
polynomial in a unary input. The program has five stacks, and a proved explicit
polynomial running time, providing the dimensions used by the tableau emitter. -/
namespace HiddenCircuits.Complexity.UnaryPolynomial
open OracleBlock Polynomial

/-- All five work registers have explicit unary contents. -/
def state (n v counter temporary product : ℕ) : Store 4 := fun i =>
  List.replicate (if i.val=0 then n else if i.val=1 then v else if i.val=2 then counter
    else if i.val=3 then temporary else product) true

noncomputable def copyInput : OracleBlock 4 := copyOn 0 2 3 (by decide) (by decide) (by decide)
noncomputable def multiplyValue : OracleBlock 4 := repeatCopy 2 1 4 3 (by decide) (by decide) (by decide)
noncomputable def moveProduct : OracleBlock 4 := reverseOn 4 1 (by decide)

noncomputable def hornerStep (a : ℕ) : OracleBlock 4 :=
  seq copyInput (seq multiplyValue (seq (clear 1) (seq moveProduct (prepend 1 (List.replicate a true)))))

theorem hornerStep_executes (g : BitString → ℕ) (n v a : ℕ) :
    (hornerStep a).Executes g (state n v 0 0 0) (state n (a+n*v) 0 0 0)
      (7*n*v+9*n+v+3*a+14) := by
  have h₁ : copyInput.Executes g (state n v 0 0 0) (state n v n 0 0) (5*n+2) := by
    have h := copyOn_executes g (0 : Fin 5) 2 3 (by decide) (by decide) (by decide) (state n v 0 0 0) rfl
    convert h using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h₂ : multiplyValue.Executes g (state n v n 0 0) (state n v 0 0 (n*v)) ((5*v+4)*n+1) := by
    have h := unaryMultiply_executes g (2 : Fin 5) 1 4 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (state n v n 0 0) n v rfl rfl rfl
    convert h using 1
    funext i;fin_cases i <;> simp [state,workStore]
  have h₃ : (clear (1 : Fin 5)).Executes g (state n v 0 0 (n*v)) (state n 0 0 0 (n*v)) (v+1) := by
    have h := clear_executes g (1 : Fin 5) (state n v 0 0 (n*v))
    convert h using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h₄ : moveProduct.Executes g (state n 0 0 0 (n*v)) (state n (n*v) 0 0 0) (2*(n*v)+1) := by
    have h := reverseOn_executes g (4 : Fin 5) 1 (by decide) (state n 0 0 0 (n*v))
    convert h using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h₅ : (prepend (1 : Fin 5) (List.replicate a true)).Executes g
      (state n (n*v) 0 0 0) (state n (a+n*v) 0 0 0) (3*a+1) := by
    have h := prepend_executes g (1 : Fin 5) (List.replicate a true) (state n (n*v) 0 0 0)
    convert h using 1
    · funext i;fin_cases i <;> simp [state,← List.replicate_add]
    · simp
  have h := seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅)))
  convert h using 1 <;> ring

lemma hornerStep_queryFree (a : ℕ) : (hornerStep a).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (repeatCopy_queryFree _ _ _ _ _ _ _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (prepend_queryFree _ _))))

noncomputable def valuePolynomial : List ℕ → Polynomial ℕ
  | [] => 0
  | a::as => C a+X*valuePolynomial as

noncomputable def timePolynomial : List ℕ → Polynomial ℕ
  | [] => 1
  | a::as => timePolynomial as+7*X*valuePolynomial as+9*X+valuePolynomial as+3*C a+16

noncomputable def evaluate : List ℕ → OracleBlock 4
  | [] => skip
  | a::as => seq (evaluate as) (hornerStep a)

theorem evaluate_executes (g : BitString → ℕ) (as : List ℕ) (n : ℕ) :
    (evaluate as).Executes g (state n 0 0 0 0) (state n ((valuePolynomial as).eval n) 0 0 0)
      ((timePolynomial as).eval n) := by
  induction as with
  | nil => simpa [evaluate,valuePolynomial,timePolynomial] using skip_executes g (state n 0 0 0 0)
  | cons a as ih =>
    have h := seq_executes _ _ g ih (hornerStep_executes g n ((valuePolynomial as).eval n) a)
    convert h using 1 <;> simp [evaluate,valuePolynomial,timePolynomial] <;> ring

lemma evaluate_queryFree (as : List ℕ) : (evaluate as).QueryFree := by
  induction as with
  | nil => exact skip_queryFree
  | cons a as ih => exact seq_queryFree _ _ ih (hornerStep_queryFree a)

def addConstant (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b::bs => (b+a)::bs

lemma addConstant_value (a : ℕ) (as : List ℕ) :
    valuePolynomial (addConstant a as) = valuePolynomial as+C a := by
  cases as <;> simp [addConstant,valuePolynomial] <;> ring

/-- The coefficient list is fixed when the polynomial is fixed. No arbitrary
input-dependent enumeration is used by the evaluating finite program. -/
theorem exists_coefficients (p : Polynomial ℕ) : ∃ as : List ℕ, valuePolynomial as = p := by
  induction p using Polynomial.recOnHorner with
  | M0 => exact ⟨[],rfl⟩
  | MC p a hp ha ih =>
    obtain ⟨as,has⟩ := ih
    exact ⟨addConstant a as,by rw [addConstant_value,has]⟩
  | MX p hp ih =>
    obtain ⟨as,has⟩ := ih
    refine ⟨0::as,?_⟩
    simp [valuePolynomial,has,mul_comm]

noncomputable def coefficients (p : Polynomial ℕ) : List ℕ := Classical.choose (exists_coefficients p)

@[simp] theorem coefficients_value (p : Polynomial ℕ) : valuePolynomial (coefficients p) = p :=
  Classical.choose_spec (exists_coefficients p)

noncomputable def polynomialBlock (p : Polynomial ℕ) : OracleBlock 4 := evaluate (coefficients p)
noncomputable def polynomialTime (p : Polynomial ℕ) : Polynomial ℕ := timePolynomial (coefficients p)

/-- Actual unary polynomial evaluation with a verified polynomial bit-operation
cost. The input is preserved, the result is on stack1, and all work stacks clear. -/
theorem polynomialBlock_executes (g : BitString → ℕ) (p : Polynomial ℕ) (n : ℕ) :
    (polynomialBlock p).Executes g (state n 0 0 0 0) (state n (p.eval n) 0 0 0)
      ((polynomialTime p).eval n) := by
  simpa only [coefficients_value] using evaluate_executes g (coefficients p) n

lemma polynomialBlock_queryFree (p : Polynomial ℕ) : (polynomialBlock p).QueryFree := evaluate_queryFree _

/-- Rename the polynomial evaluator into arbitrary surrounding data while
changing only its result register. All three scratch registers are restored. -/
theorem polynomialOn_executes {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (g : BitString → ℕ)
    (p : Polynomial ℕ) (n : ℕ) (outer : Store k) (houter : outer ∘ φ = state n 0 0 0 0) :
    (rename (polynomialBlock p) φ).Executes g outer
      (Function.update outer (φ 1) (List.replicate (p.eval n) true)) ((polynomialTime p).eval n) := by
  apply rename_executes_to _ φ g (polynomialBlock_executes g p n) houter
  · funext i
    by_cases hi : i=1
    · subst i;simp [Function.comp_def,state]
    · have hφ : φ i ≠ φ 1 := fun h => hi (φ.injective h)
      simp only [Function.comp_def,Function.update_of_ne hφ]
      have h := congrFun houter i
      simpa only [Function.comp_def] using h.trans (by fin_cases i <;> simp_all [state])
  · intro i hi
    exact Function.update_of_ne (fun h => hi 1 h.symm) _ _

end HiddenCircuits.Complexity.UnaryPolynomial
