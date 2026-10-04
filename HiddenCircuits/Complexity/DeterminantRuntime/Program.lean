import HiddenCircuits.Complexity.DeterminantRuntime.Input
import HiddenCircuits.Complexity.DeterminantRuntime.Prepare
import HiddenCircuits.Complexity.DeterminantRuntime.Loop
import HiddenCircuits.Complexity.DeterminantRuntime.Sign

/-! Fixed, query-free, polynomial-bit-time canonical integer determinant
evaluation. All scratch is physically cleared; all off-bank stacks are framed. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open OracleBlock BinaryArithmetic Polynomial

noncomputable def dirtyProgram : OracleBlock 30 := seq Input.program
  (seq Prepare.program (seq loopProgram Sign.program))

noncomputable def dirtyTime : Polynomial ℕ := IdentityMatrix.time+
  X*(Round.timePolynomial.comp (100*(X+1)^4)+5)+30*X+100

theorem dirty_executes (g : BitString → ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ t, dirtyProgram.Executes g (Input.store (matrixInput A))
      (Round.store n (encodeBitList (matrixWords A))
        (encodeBitList (matrixWords (faddeevState A n).1)) (signedBits A.det) n 0) t ∧
      t ≤ dirtyTime.eval (matrixInput A).length := by
  obtain ⟨a,ha,hab⟩ := Prepare.executes g n (encodeBitList (matrixWords A))
  obtain ⟨b,hb,hbb⟩ := loop_executes g A
  obtain ⟨c,hc,hcb⟩ := Sign.executes g n (encodeBitList (matrixWords A))
    (encodeBitList (matrixWords (faddeevState A n).1)) (faddeevState A n).2 n 0
  have he : (-1)^n*(faddeevState A n).2 = A.det := determinant_eq_det A
  rw [he] at hc
  have h := seq_executes _ _ g (Input.executes g n (encodeBitList (matrixWords A)))
    (seq_executes _ _ g ha (seq_executes _ _ g hb hc))
  refine ⟨_,h,?_⟩
  have hn := dimension_le_input A
  have harr := array_length_le_input A
  have hm := polynomial_nat_eval_mono IdentityMatrix.time hn
  have hl := Nat.mul_le_mul_right (Round.timePolynomial.eval (roundSizeBound A)+5) hn
  simp only [dirtyTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_one]
  dsimp only at hm
  unfold roundSizeBound at hl hbb
  omega

noncomputable def program : OracleBlock 30 := seq dirtyProgram (cleanResult 3 6 (by decide) (by decide))
noncomputable def timePolynomial : Polynomial ℕ := dirtyTime+35*(X+dirtyTime+3)+3

/-- No coefficient, determinant, size, or runtime certificate is supplied.
The bound is a closed natural polynomial of the actual encoded input length. -/
theorem canonical_executes (g : BitString → ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ t, program.Executes g (Input.store (matrixInput A)) (Input.store (signedBits A.det)) t ∧
      t ≤ timePolynomial.eval (matrixInput A).length := by
  obtain ⟨t,ht,hb⟩ := dirty_executes g A
  let s := Round.store n (encodeBitList (matrixWords A))
    (encodeBitList (matrixWords (faddeevState A n).1)) (signedBits A.det) n 0
  have hi : ∀ q, (Input.store (matrixInput A) q).length ≤ (matrixInput A).length := by
    intro q
    by_cases hq : q=0
    · subst q;simp [Input.store]
    · simp [Input.store,hq]
  have hs : ∀ q, (s q).length ≤ (matrixInput A).length+t := ht.stack_bound hi
  obtain ⟨c,hc,hcb⟩ := cleanResult_executes g (3 : Fin 31) 6 (by decide) (by decide) (by decide)
    s ((matrixInput A).length+t) hs
  refine ⟨_,seq_executes _ _ g ht hc,?_⟩
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

theorem dirtyProgram_queryFree : dirtyProgram.QueryFree := seq_queryFree _ _ Input.queryFree
  (seq_queryFree _ _ Prepare.queryFree (seq_queryFree _ _ loopProgram_queryFree Sign.queryFree))

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ dirtyProgram_queryFree (cleanResult_queryFree _ _ _ _)

noncomputable def on {k : ℕ} (φ : Fin 31 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 31 ↪ Fin (k+1)) (g : BitString → ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (s : Store k) (hs : s ∘ φ = Input.store (matrixInput A)) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 0) (signedBits A.det)) t ∧
      t ≤ timePolynomial.eval (matrixInput A).length := by
  obtain ⟨t,ht,hb⟩ := canonical_executes g A
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 0) (signedBits A.det)) ∘ φ =
        Function.update (s ∘ φ) 0 (signedBits A.det) := by
      funext q;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    simp [Input.store,Function.update_idem]
  · intro q hq;exact Function.update_of_ne (hq 0).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 31 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Complexity.DeterminantRuntime
