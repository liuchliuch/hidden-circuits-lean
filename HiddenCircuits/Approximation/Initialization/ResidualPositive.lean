import HiddenCircuits.Approximation.Initialization.ResidualPositiveData
import HiddenCircuits.Approximation.Initialization.ResidualMatrixProgram
import HiddenCircuits.Approximation.Initialization.SignedNonzero
import HiddenCircuits.Complexity.DeterminantRuntime.Program
import HiddenCircuits.Complexity.PolynomialBounds

/-! The fully instantiated36-stack residual determinant test. The
actual matrix builder and actual integer determinant machine are composed;
there is no determinant, runtime, or matching certificate parameter. -/
namespace HiddenCircuits.Approximation.Initialization.ResidualPositive
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def state (N : ℕ) (payload mask tape : BitString) (B : ℕ) (out matrix : BitString) : Store 35 := fun r =>
  if r.val=0 then List.replicate N true else if r.val=1 then payload else if r.val=2 then mask
  else if r.val=3 then tape else if r.val=4 then List.replicate B true else if r.val=5 then out
  else if r.val=6 then matrix else []

def matrixPorts : Fin 27 ↪ Fin 36 where
  toFun r := if r.val<5 then ⟨r.val,by omega⟩ else ⟨r.val+1,by omega⟩
  inj' := by decide +kernel
def determinantPorts : Fin 31 ↪ Fin 36 where
  toFun r := if r.val=0 then 6 else if r.val=1 then 5 else ⟨r.val+5,by omega⟩
  inj' := by decide +kernel
def resultPorts : Fin 2 ↪ Fin 36 where
  toFun r := if r.val=0 then 6 else 5
  inj' := by decide +kernel

noncomputable def program : OracleBlock 35 := seq (ResidualMatrixProgram.on matrixPorts)
  (seq (DeterminantRuntime.on determinantPorts) (rename SignedNonzero.program resultPorts))

def matrixLength (N B : ℕ) : ℕ := 2*N+1+N*N*(2*(B+1)+2)
noncomputable def timeBound (N B T : ℕ) : ℕ := ResidualMatrixProgram.timeBound N B T+
  matrixLength N B+2*DeterminantRuntime.timePolynomial.eval (matrixLength N B)+11

theorem matrix_length {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString) :
    (DeterminantRuntime.matrixInput (ResidualMatrixProgram.matrix G U B tape)).length ≤ matrixLength N B := by
  have hh := MatrixInputProgram.matrix_length (InducedGraphEmitter.induced G U) B tape
  have hn : U.card ≤ N := by simpa using U.card_le_univ
  apply hh.trans
  unfold matrixLength
  gcongr

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N)
    (U : Finset (Fin N)) (B : ℕ) (tape : BitString) :
    ∃ t, program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) tape B [] [])
      (state N G.bits (MaskEnumerationSemantics.mask U) tape B [positive G U B tape] []) t ∧
      t ≤ timeBound N B tape.length := by
  let M := MaskEnumerationSemantics.mask U
  let A := ResidualMatrixProgram.matrix G U B tape
  let I := DeterminantRuntime.matrixInput A
  obtain ⟨a,ha,hab⟩ := ResidualMatrixProgram.on_executes matrixPorts g
    (state N G.bits M tape B [] []) G U B tape (by funext r;fin_cases r <;> rfl)
  have h1 : (ResidualMatrixProgram.on matrixPorts).Executes g (state N G.bits M tape B [] [])
      (state N G.bits M tape B [] I) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,matrixPorts,I,A]
  obtain ⟨b,hb,hbb⟩ := DeterminantRuntime.canonical_executes g A
  have hi : ∀ r, (DeterminantRuntime.Input.store I r).length ≤ I.length := by
    intro r
    by_cases h : r=0
    · subst r;simp [DeterminantRuntime.Input.store]
    · simp [DeterminantRuntime.Input.store,h]
  have hout := hb.stack_bound hi (0 : Fin 31)
  change (signedBits A.det).length ≤ I.length+b at hout
  have h2 : (DeterminantRuntime.on determinantPorts).Executes g (state N G.bits M tape B [] I)
      (state N G.bits M tape B [] (signedBits A.det)) b := by
    apply rename_executes_to DeterminantRuntime.program determinantPorts g hb
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r
      all_goals first | rfl | exact (hr 0 rfl).elim
  obtain ⟨c,hc,hcb⟩ := SignedNonzero.program_executes g A.det
  have h3 : (rename SignedNonzero.program resultPorts).Executes g
      (state N G.bits M tape B [] (signedBits A.det))
      (state N G.bits M tape B [positive G U B tape] []) c := by
    apply rename_executes_to SignedNonzero.program resultPorts g hc
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r
      all_goals first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hl : I.length ≤ matrixLength N B := matrix_length G U B tape
  have hd := polynomial_nat_eval_mono DeterminantRuntime.timePolynomial hl
  have hbb' := hbb.trans hd
  change b ≤ DeterminantRuntime.timePolynomial.eval (matrixLength N B) at hbb'
  unfold timeBound
  omega

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (ResidualMatrixProgram.on_queryFree _)
  (seq_queryFree _ _ (DeterminantRuntime.on_queryFree _) (rename_queryFree _ _ SignedNonzero.program_queryFree))

noncomputable def on {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) : OracleBlock k := rename program φ
theorem on_executes {k N : ℕ} (φ : Fin 36 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString)
    (hs : s ∘ φ = state N G.bits (MaskEnumerationSemantics.mask U) tape B [] []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 5) [positive G U B tape]) t ∧
      t ≤ timeBound N B tape.length := by
  obtain ⟨t,ht,hb⟩ := program_executes g G U B tape
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases r <;> rfl
  · intro r hr
    exact Function.update_of_ne (hr 5).symm _ _
theorem on_queryFree {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.ResidualPositive
