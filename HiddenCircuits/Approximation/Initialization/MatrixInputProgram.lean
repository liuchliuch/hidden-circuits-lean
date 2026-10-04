import HiddenCircuits.Approximation.Initialization.TapeWordsFrame
import HiddenCircuits.Approximation.Initialization.TutteMatrixEmitter

/-! The full23-stack raw graph/tape-to-integer-matrix input compiler.
The graph and raw source are preserved; every scratch register is cleared. -/
namespace HiddenCircuits.Approximation.Initialization.MatrixInputProgram
open Complexity Complexity.OracleBlock Complexity.GraphVerifier.Runtime

def state (n : ℕ) (payload tape : BitString) (B : ℕ)
    (out count counter source words : BitString) : Store 22 := fun r =>
  if r.val=0 then List.replicate n true else if r.val=1 then payload else if r.val=2 then tape
  else if r.val=3 then List.replicate B true else if r.val=4 then out else if r.val=5 then count
  else if r.val=6 then counter else if r.val=7 then source else if r.val=8 then words else []

def productPorts : Fin 4 ↪ Fin 23 where
  toFun r := if r.val=0 then 0 else if r.val=1 then 5 else if r.val=2 then 6 else 9
  inj' := by decide +kernel
def tapePorts : Fin 8 ↪ Fin 23 where
  toFun r := if r.val=0 then 7 else if r.val=1 then 3 else if r.val=2 then 6
    else if r.val=3 then 10 else if r.val=4 then 11 else if r.val=5 then 12
    else if r.val=6 then 8 else 9
  inj' := by decide +kernel
def emitPorts : Fin 21 ↪ Fin 23 where
  toFun r := if r.val=0 then 0 else if r.val=1 then 5 else if r.val=2 then 6 else if r.val=3 then 7
    else if r.val=4 then 9 else if r.val=5 then 10 else if r.val=6 then 11 else if r.val=7 then 4
    else if r.val=8 then 1 else if r.val=9 then 8 else ⟨r.val+2,by omega⟩
  inj' := by decide +kernel

noncomputable def program : OracleBlock 22 :=
  seq (copyOn 0 5 9 (by decide) (by decide) (by decide))
    (seq (rename repeatCopyBlock productPorts)
      (seq (copyOn 2 7 9 (by decide) (by decide) (by decide))
        (seq (TapeWords.on tapePorts) (seq (TutteMatrixEmitter.on emitPorts) (clear 8)))))

def timeBound (n B T L : ℕ) : ℕ :=
  5*n+2+((5*n+4)*n+1)+2+(5*T+2)+2+(n*n*(23*B+26)+T+7)+
    TutteMatrixEmitter.timeBound n L+L+7

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n)
    (B : ℕ) (tape : BitString) :
    ∃ t, program.Executes g (state n G.bits tape B [] [] [] [] [])
      (state n G.bits tape B (DeterminantRuntime.matrixInput (TutteInteger.matrix G.graph B tape)) [] [] [] []) t ∧
      t ≤ timeBound n B tape.length (encodeBitList (TapeWords.words B (n*n) tape)).length := by
  let I := encodeBitList (TapeWords.words B (n*n) tape)
  let x : Fin (n*n) → ℕ := fun e => TutteInteger.number B tape e.val
  have hw : TutteEntry.randomWords x = TapeWords.words B (n*n) tape := (TapeWords.words_ofFn B (n*n) tape).symm
  have h1 : (copyOn (0 : Fin 23) 5 9 (by decide) (by decide) (by decide)).Executes g
      (state n G.bits tape B [] [] [] [] [])
      (state n G.bits tape B [] (List.replicate n true) [] [] []) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 23) 5 9 (by decide) (by decide) (by decide)
      (state n G.bits tape B [] [] [] [] []) rfl using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h2 : (rename repeatCopyBlock productPorts).Executes g
      (state n G.bits tape B [] (List.replicate n true) [] [] [])
      (state n G.bits tape B [] [] (List.replicate (n*n) true) [] []) (n*(5*n+4)+1) := by
    have hh := repeatCopy_execution g (List.replicate n true) (List.replicate n true) (List.replicate 0 true)
    simp only [List.length_replicate,repeatPrefix_unary,List.length_nil,Nat.add_zero] at hh
    apply rename_executes_to repeatCopyBlock productPorts g hh
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r
      all_goals first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim | exact (hr 2 rfl).elim | exact (hr 3 rfl).elim
  have h3 : (copyOn (2 : Fin 23) 7 9 (by decide) (by decide) (by decide)).Executes g
      (state n G.bits tape B [] [] (List.replicate (n*n) true) [] [])
      (state n G.bits tape B [] [] (List.replicate (n*n) true) tape []) (5*tape.length+2) := by
    convert copyOn_executes g (2 : Fin 23) 7 9 (by decide) (by decide) (by decide)
      (state n G.bits tape B [] [] (List.replicate (n*n) true) [] []) rfl using 1
    funext r;fin_cases r <;> simp [state]
  obtain ⟨a,ha,hab⟩ := TapeWords.on_executes tapePorts g
    (state n G.bits tape B [] [] (List.replicate (n*n) true) tape []) tape B (n*n)
    (by funext r;fin_cases r <;> rfl)
  have h4 : (TapeWords.on tapePorts).Executes g
      (state n G.bits tape B [] [] (List.replicate (n*n) true) tape [])
      (state n G.bits tape B [] [] [] [] I) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,tapePorts,I]
  obtain ⟨b,hb,hbb⟩ := TutteMatrixEmitter.on_executes emitPorts g
    (state n G.bits tape B [] [] [] [] I) G x
    (by funext r;fin_cases r <;> simp [state,emitPorts,TutteMatrixEmitter.initial,TutteEntry.params,
      MatrixEmitter.store,MatrixEmitter.port,hw,I])
  rw [hw] at hbb
  have h5 : (TutteMatrixEmitter.on emitPorts).Executes g (state n G.bits tape B [] [] [] [] I)
      (state n G.bits tape B (DeterminantRuntime.matrixInput (TutteInteger.matrix G.graph B tape)) [] [] [] I) b := by
    convert hb using 1
    funext r;fin_cases r <;> simp [state,emitPorts,TutteInteger.matrix,x]
  have h6 : (clear (8 : Fin 23)).Executes g
      (state n G.bits tape B (DeterminantRuntime.matrixInput (TutteInteger.matrix G.graph B tape)) [] [] [] I)
      (state n G.bits tape B (DeterminantRuntime.matrixInput (TutteInteger.matrix G.graph B tape)) [] [] [] [])
      (I.length+1) := by
    convert clear_executes g (8 : Fin 23) _ using 1
    funext r;fin_cases r <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  unfold timeBound
  dsimp only [I] at *
  nlinarith

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ repeatCopy_queryFree)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (TapeWords.on_queryFree _)
        (seq_queryFree _ _ (TutteMatrixEmitter.on_queryFree _) (clear_queryFree _)))))

end HiddenCircuits.Approximation.Initialization.MatrixInputProgram
