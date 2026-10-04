import HiddenCircuits.Complexity.InitialRowProgram

/-! Polynomial bit-time and fully cleaned arbitrary-stack endpoints for the
actual initial-row emitter. Only the semantic height precondition is required. -/
namespace HiddenCircuits.Complexity.InitialRowEmitter
open OracleBlock TM2BooleanEncoding Polynomial
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def controlTime : Polynomial ℕ :=
  C (controlBits M.tm)*(64*(2*X+2*C (controlBits M.tm)+X*C (symbolBits M.tm))+220)+1
noncomputable def symbolTime : Polynomial ℕ :=
  C (symbolBits M.tm)*(64*(2*X+C (controlBits M.tm)+X*C (symbolBits M.tm)+C (symbolBits M.tm))+220)+1
noncomputable def time : Polynomial ℕ := 20*X+34+controlTime M+X*(symbolTime M+8)

lemma family_bounds (x : BitString) (m H : ℕ) :
    familyBound m (m+bitCount M.tm H) (controlBits M.tm) ≤ (controlTime M).eval (x.length+m+H) ∧
    familyBound m (m+bitCount M.tm H) (symbolBits M.tm) ≤ (symbolTime M).eval (x.length+m+H) := by
  have hm : m≤x.length+m+H := by omega
  have hH : H≤x.length+m+H := by omega
  have hS := Nat.mul_le_mul_right (symbolBits M.tm) hH
  constructor
  · have hi : 64*(m+(m+bitCount M.tm H)+controlBits M.tm)+220 ≤
        64*(2*(x.length+m+H)+2*controlBits M.tm+(x.length+m+H)*symbolBits M.tm)+220 := by
      unfold bitCount;omega
    have h := Nat.mul_le_mul_left (controlBits M.tm) hi
    simpa [familyBound,controlTime] using Nat.add_le_add_right h 1
  · have hi : 64*(m+(m+bitCount M.tm H)+symbolBits M.tm)+220 ≤
        64*(2*(x.length+m+H)+controlBits M.tm+(x.length+m+H)*symbolBits M.tm+symbolBits M.tm)+220 := by
      unfold bitCount;omega
    have h := Nat.mul_le_mul_left (symbolBits M.tm) hi
    simpa [familyBound,symbolTime] using Nat.add_le_add_right h 1

theorem program_polynomial (g : BitString → ℕ) (x : BitString) (m H : ℕ)
    (hH : 2*x.length+m+1≤H) (stream : BitString) :
    ∃ cost, (program M).Executes g (state 0 0 x m H [] 0 0 stream)
      (state m (m+bitCount M.tm H) x m H [] 0 0 ((bits M x m H).reverse++stream)) cost ∧
      cost ≤ (time M).eval (x.length+m+H) := by
  obtain ⟨c,hc,hb⟩ := program_executes M g x m H hH stream
  refine ⟨c,hc,?_⟩
  obtain ⟨hC,hS⟩ := family_bounds M x m H
  have hp := Nat.mul_le_mul (show H≤x.length+m+H by omega) (Nat.add_le_add_right hS 8)
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

noncomputable def cleanProgram : OracleBlock 11 := seq (program M) (seq (clear 0) (clear 1))
noncomputable def cleanTime : Polynomial ℕ :=
  time M+2*X+C (controlBits M.tm)+X*C (symbolBits M.tm)+6

theorem cleanProgram_executes (g : BitString → ℕ) (x : BitString) (m H : ℕ)
    (hH : 2*x.length+m+1≤H) (stream : BitString) :
    ∃ cost, (cleanProgram M).Executes g (state 0 0 x m H [] 0 0 stream)
      (state 0 0 x m H [] 0 0 ((bits M x m H).reverse++stream)) cost ∧
      cost ≤ (cleanTime M).eval (x.length+m+H) := by
  obtain ⟨c,hc,hb⟩ := program_polynomial M g x m H hH stream
  let out := (bits M x m H).reverse++stream
  have h0 : (clear (0 : Fin 12)).Executes g (state m (m+bitCount M.tm H) x m H [] 0 0 out)
      (state 0 (m+bitCount M.tm H) x m H [] 0 0 out) (m+1) := by
    convert clear_executes g (0 : Fin 12) (state m (m+bitCount M.tm H) x m H [] 0 0 out) using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h1 : (clear (1 : Fin 12)).Executes g (state 0 (m+bitCount M.tm H) x m H [] 0 0 out)
      (state 0 0 x m H [] 0 0 out) (m+bitCount M.tm H+1) := by
    convert clear_executes g (1 : Fin 12) (state 0 (m+bitCount M.tm H) x m H [] 0 0 out) using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  refine ⟨c+(m+1+(m+bitCount M.tm H+1)+2)+2,seq_executes _ _ g hc (seq_executes _ _ g h0 h1),?_⟩
  have hm := Nat.mul_le_mul_right (symbolBits M.tm) (show H≤x.length+m+H by omega)
  simp only [cleanTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_C]
  unfold bitCount
  omega

lemma cleanProgram_queryFree : (cleanProgram M).QueryFree :=
  seq_queryFree _ _ (program_queryFree M) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))

noncomputable def cleanProgramOn {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) : OracleBlock k := rename (cleanProgram M) φ

theorem cleanProgramOn_executes {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) (g : BitString → ℕ)
    (outer : Store k) (x : BitString) (m H : ℕ) (hH : 2*x.length+m+1≤H)
    (hs : outer ∘ φ=state 0 0 x m H [] 0 0 (outer (φ 4))) :
    ∃ cost, (cleanProgramOn M φ).Executes g outer
      (Function.update outer (φ 4) ((bits M x m H).reverse++outer (φ 4))) cost ∧
      cost ≤ (cleanTime M).eval (x.length+m+H) := by
  obtain ⟨c,hc,hb⟩ := cleanProgram_executes M g x m H hH (outer (φ 4))
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · have he : (Function.update outer (φ 4) ((bits M x m H).reverse++outer (φ 4))) ∘ φ =
        Function.update (outer ∘ φ) 4 ((bits M x m H).reverse++outer (φ 4)) := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi
    exact Function.update_of_ne (hi 4).symm _ _

lemma cleanProgramOn_queryFree {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) :
    (cleanProgramOn M φ).QueryFree := rename_queryFree _ _ (cleanProgram_queryFree M)

end HiddenCircuits.Complexity.InitialRowEmitter
