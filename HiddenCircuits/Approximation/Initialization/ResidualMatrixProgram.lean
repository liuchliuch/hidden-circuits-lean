import HiddenCircuits.Approximation.Initialization.ResidualGraphFrame
import HiddenCircuits.Approximation.Initialization.MatrixInputSemantics

/-! Complete retained-mask to integer Tutte input construction. The
induced graph is physically emitted, parsed, and passed to the matrix builder. -/
namespace HiddenCircuits.Approximation.Initialization.ResidualMatrixProgram
open Complexity Complexity.OracleBlock GraphVerifier GraphVerifier.Runtime

def matrix {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString) :=
  TutteInteger.matrix (ResidualTest.graph G.graph U) B tape

def state (N : ℕ) (payload mask tape : BitString) (B : ℕ)
    (out graph header flag : BitString) : Store 26 := fun r =>
  if r.val=0 then List.replicate N true else if r.val=1 then payload else if r.val=2 then mask
  else if r.val=3 then tape else if r.val=4 then List.replicate B true else if r.val=5 then out
  else if r.val=6 then graph else if r.val=7 then header else if r.val=9 then flag else []

def graphPorts : Fin 18 ↪ Fin 27 where
  toFun r := if r.val<3 then ⟨r.val,by omega⟩ else if r.val=3 then 6
    else ⟨r.val+6,by omega⟩
  inj' := by decide +kernel
def parsePorts : Fin 4 ↪ Fin 27 where
  toFun r := ⟨r.val+6,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh:=congrArg Fin.val h;dsimp at hh;omega
def matrixPorts : Fin 23 ↪ Fin 27 where
  toFun r := if r.val=0 then 7 else if r.val=1 then 6 else if r.val=2 then 3
    else if r.val=3 then 4 else if r.val=4 then 5 else ⟨r.val+4,by omega⟩
  inj' := by decide +kernel

noncomputable def program : OracleBlock 26 := seq (ResidualGraphProgram.on graphPorts)
  (seq (unpairOn parsePorts) (seq (clear 9)
    (seq (MatrixInputProgram.on matrixPorts) (seq (clear 6) (clear 7)))))

def timeBound (N B T : ℕ) : ℕ := ResidualGraphProgram.timeBound N N (N*(2*N+2))+
  3*(2*N+1+N*N)+8+MatrixInputProgram.timeBound N B T (N*N*(2*B+2))+N*N+N+10

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N)
    (U : Finset (Fin N)) (B : ℕ) (tape : BitString) :
    ∃ t, program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) tape B [] [] [] [])
      (state N G.bits (MaskEnumerationSemantics.mask U) tape B
        (DeterminantRuntime.matrixInput (matrix G U B tape)) [] [] []) t ∧
      t ≤ timeBound N B tape.length := by
  let M := MaskEnumerationSemantics.mask U
  let H := InducedGraphEmitter.induced G U
  let Q := GraphInput.encode ⟨U.card,H⟩
  let C := List.replicate U.card true
  let A := DeterminantRuntime.matrixInput (matrix G U B tape)
  obtain ⟨a,ha,hab⟩ := ResidualGraphProgram.on_executes graphPorts g
    (state N G.bits M tape B [] [] [] []) G U (by funext r;fin_cases r <;> rfl)
  have h1 : (ResidualGraphProgram.on graphPorts).Executes g (state N G.bits M tape B [] [] [] [])
      (state N G.bits M tape B [] Q [] []) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,graphPorts,Q,H]
  have h2 : (unpairOn parsePorts).Executes g (state N G.bits M tape B [] Q [] [])
      (state N G.bits M tape B [] H.bits C [true]) (5*U.card+3) := by
    convert unpairOn_executes parsePorts g (state N G.bits M tape B [] Q [] [])
      (state N G.bits M tape B [] H.bits C [true]) Q
      (by funext r;fin_cases r <;> rfl)
      (by simp only [Q,GraphInput.encode,parse_pair];funext r;fin_cases r <;> rfl)
      (by intro r hr;fin_cases r
          all_goals first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim | exact (hr 2 rfl).elim | exact (hr 3 rfl).elim) using 1
    simp [Q,GraphInput.encode,parse_pair,BinaryArithmetic.pair_parse_cost]
    omega
  have h3 : (clear (9 : Fin 27)).Executes g (state N G.bits M tape B [] H.bits C [true])
      (state N G.bits M tape B [] H.bits C []) 2 := by
    convert clear_executes g (9 : Fin 27) _ using 1
    funext r;fin_cases r <;> rfl
  obtain ⟨b,hb,hbb⟩ := MatrixInputProgram.on_executes matrixPorts g
    (state N G.bits M tape B [] H.bits C []) H B tape (by funext r;fin_cases r <;> rfl)
  have h4 : (MatrixInputProgram.on matrixPorts).Executes g (state N G.bits M tape B [] H.bits C [])
      (state N G.bits M tape B A H.bits C []) b := by
    convert hb using 1
    funext r;fin_cases r <;> simp [state,matrixPorts,A,matrix,H,InducedGraphEmitter.induced_graph]
  have h5 : (clear (6 : Fin 27)).Executes g (state N G.bits M tape B A H.bits C [])
      (state N G.bits M tape B A [] C []) (U.card*U.card+1) := by
    convert clear_executes g (6 : Fin 27) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state,H]
  have h6 : (clear (7 : Fin 27)).Executes g (state N G.bits M tape B A [] C [])
      (state N G.bits M tape B A [] [] []) (U.card+1) := by
    convert clear_executes g (7 : Fin 27) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state,C]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  have hn : U.card ≤ N := by simpa using U.card_le_univ
  have hsq := Nat.mul_le_mul hn hn
  have htime : MatrixInputProgram.timeBound U.card B tape.length (U.card*U.card*(2*B+2)) ≤
      MatrixInputProgram.timeBound N B tape.length (N*N*(2*B+2)) :=
    MatrixInputProgram.timeBound_mono hn le_rfl le_rfl (Nat.mul_le_mul_right (2*B+2) hsq)
  have hb' := hbb.trans htime
  unfold timeBound
  nlinarith

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (ResidualGraphProgram.on_queryFree _)
  (seq_queryFree _ _ (unpairOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (MatrixInputProgram.on_queryFree _)
      (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))))

noncomputable def on {k : ℕ} (φ : Fin 27 ↪ Fin (k+1)) : OracleBlock k := rename program φ
theorem on_executes {k N : ℕ} (φ : Fin 27 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString)
    (hs : s ∘ φ = state N G.bits (MaskEnumerationSemantics.mask U) tape B [] [] [] []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 5)
      (DeterminantRuntime.matrixInput (matrix G U B tape))) t ∧ t ≤ timeBound N B tape.length := by
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
theorem on_queryFree {k : ℕ} (φ : Fin 27 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.ResidualMatrixProgram
