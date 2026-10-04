import HiddenCircuits.Complexity.PortIndexEmitter
import HiddenCircuits.Complexity.CNFEmitter
import HiddenCircuits.Complexity.PolynomialBounds

/-! Complete actual port-literal emission, including row-address generation and
serialization, with polynomial bit time and complete metadata preservation. -/
namespace HiddenCircuits.Complexity.PortLiteralEmitter
open OracleBlock TM2BooleanEncoding Polynomial

def state (position base index counter temporary right : ℕ) (stream : BitString) : Store 6 := fun i =>
  if i.val=6 then stream else List.replicate (if i.val=0 then position else if i.val=1 then base
    else if i.val=2 then index else if i.val=3 then counter else if i.val=4 then temporary else right) true

noncomputable def indexProgram (M : Turing.FinTM2) (p : Port M) : OracleBlock 6 :=
  rename (PortIndexEmitter.program M p) (Fin.castAddEmb 1)

theorem indexProgram_executes (g : BitString → ℕ) (M : Turing.FinTM2) (p : Port M)
    (j r base : ℕ) (stream : BitString) :
    ∃ cost, (indexProgram M p).Executes g (state j base 0 0 0 r stream)
      (state j base (base+portAddress M (j+r+1) j p) 0 0 r stream) cost ∧
      cost ≤ (PortIndexEmitter.time M p).eval (j+base) := by
  obtain ⟨cost,hc,hb⟩ := PortIndexEmitter.program_executes g M p j r base
  refine ⟨cost,?_,hb⟩
  apply rename_executes_to _ (Fin.castAddEmb 1) g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact (hi 0 rfl).elim
    · exact (hi 1 rfl).elim
    · exact (hi 2 rfl).elim
    · exact (hi 3 rfl).elim
    · exact (hi 4 rfl).elim
    · exact (hi 5 rfl).elim
    · rfl

noncomputable def program (M : Turing.FinTM2) (p : Port M) (sign : Bool) : OracleBlock 6 :=
  seq (indexProgram M p) (CNFEmitter.literal 2 6 sign)

noncomputable def time (M : Turing.FinTM2) (p : Port M) : Polynomial ℕ :=
  PortIndexEmitter.time M p+27*(X+C (controlBits M)+(X+1)*C (symbolBits M))+45

lemma index_bound (M : Turing.FinTM2) (p : Port M) (j r base : ℕ) :
    base+portAddress M (j+r+1) j p ≤
      j+r+base+controlBits M+(j+r+base+1)*symbolBits M := by
  have h : portAddress M (j+r+1) j p < bitCount M (j+r+1) := by
    rw [portAddress_correct]
    exact (cellEnumeration M (j+r+1) (portCell M (j+r+1) j p)).isLt
  have hm := Nat.mul_le_mul_right (symbolBits M) (show j+r+1 ≤ j+r+base+1 by omega)
  unfold bitCount at h
  omega

/-- A real finite code block generates the exact literal indexed by the actual
TM2 port, restoring both distance counters and the row base. -/
theorem program_executes (g : BitString → ℕ) (M : Turing.FinTM2) (p : Port M)
    (sign : Bool) (j r base : ℕ) (stream : BitString) :
    ∃ cost, (program M p sign).Executes g (state j base 0 0 0 r stream)
      (state j base 0 0 0 r ((serializedLiteral (base+portAddress M (j+r+1) j p) sign).reverse++stream)) cost ∧
      cost ≤ (time M p).eval (j+r+base) := by
  obtain ⟨ci,hi,hbi⟩ := indexProgram_executes g M p j r base stream
  let index := base+portAddress M (j+r+1) j p
  have hl : (CNFEmitter.literal (2 : Fin 7) 6 sign).Executes g
      (state j base index 0 0 r stream)
      (state j base 0 0 0 r ((serializedLiteral index sign).reverse++stream)) (27*index+43) := by
    have h := CNFEmitter.literal_executes g (2 : Fin 7) 6 (by decide) sign (state j base index 0 0 r stream)
    convert h using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have hs := seq_executes _ _ g hi hl
  refine ⟨ci+(27*index+43)+2,hs,?_⟩
  have hmono := polynomial_nat_eval_mono (PortIndexEmitter.time M p) (show j+base ≤ j+r+base by omega)
  dsimp only at hmono
  have hidx := index_bound M p j r base
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,
    Polynomial.eval_one,Polynomial.eval_ofNat]
  dsimp only [index]
  omega

lemma program_queryFree (M : Turing.FinTM2) (p : Port M) (sign : Bool) : (program M p sign).QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ (PortIndexEmitter.program_queryFree _ _)) (CNFEmitter.literal_queryFree _ _ _)

end HiddenCircuits.Complexity.PortLiteralEmitter
