import HiddenCircuits.Approximation.Initialization.InducedGraphEmitter

/-! Complete mask-to-induced-graph serialization, with every temporary
count, address word, and emitter register physically cleared. -/
namespace HiddenCircuits.Approximation.Initialization.ResidualGraphProgram
open Complexity Complexity.OracleBlock

def state (N : ℕ) (payload mask out count ids : BitString) : Store 17 := fun r =>
  if r.val=0 then List.replicate N true else if r.val=1 then payload else if r.val=2 then mask
  else if r.val=3 then out else if r.val=4 then count else if r.val=5 then ids else []

def enumPorts : Fin 7 ↪ Fin 18 where
  toFun r := if r.val=0 then 2 else if r.val=1 then 4 else if r.val=2 then 6
    else if r.val=3 then 7 else if r.val=4 then 5 else if r.val=5 then 8 else 9
  inj' := by decide +kernel

def emitPorts : Fin 17 ↪ Fin 18 where
  toFun r := if r.val=0 then 4 else if h : r.val<7 then ⟨r.val+5,by omega⟩
    else if r.val=7 then 3 else if r.val=8 then 0 else if r.val=9 then 1
    else if r.val=10 then 5 else ⟨r.val+1,by omega⟩
  inj' := by decide +kernel

noncomputable def program : OracleBlock 17 :=
  seq (MaskEnumeration.on enumPorts) (seq (InducedGraphEmitter.on emitPorts)
    (seq (clear 4) (clear 5)))

def timeBound (N n L : ℕ) : ℕ := 5*N+55*(N+1)^2+4+
  InducedGraphEmitter.timeBound N n L+n+L+8

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) :
    ∃ t, program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) [] [] [])
      (state N G.bits (MaskEnumerationSemantics.mask U)
        (GraphInput.encode ⟨U.card,InducedGraphEmitter.induced G U⟩) [] []) t ∧
      t ≤ timeBound N U.card (encodeBitList (InducedGraphEmitter.indexWords U)).length := by
  let M := MaskEnumerationSemantics.mask U
  let I := encodeBitList (InducedGraphEmitter.indexWords U)
  let E := GraphInput.encode ⟨U.card,InducedGraphEmitter.induced G U⟩
  obtain ⟨a,ha,hab⟩ := MaskEnumeration.on_executes enumPorts g (state N G.bits M [] [] []) U
    (by funext r;fin_cases r <;> rfl)
  have h1 : (MaskEnumeration.on enumPorts).Executes g (state N G.bits M [] [] [])
      (state N G.bits M [] (List.replicate U.card true) I) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,enumPorts,I,InducedGraphEmitter.indexWords]
  obtain ⟨b,hb,hbb⟩ := InducedGraphEmitter.on_executes emitPorts g
    (state N G.bits M [] (List.replicate U.card true) I) G U
    (by funext r;fin_cases r <;>
      simp [state,emitPorts,InducedGraphEmitter.initial,InducedEntry.params,
        MatrixEmitter.store,MatrixEmitter.port,I])
  have h2 : (InducedGraphEmitter.on emitPorts).Executes g
      (state N G.bits M [] (List.replicate U.card true) I)
      (state N G.bits M E (List.replicate U.card true) I) b := by
    convert hb using 1
    funext r;fin_cases r <;> simp [state,emitPorts,E]
  have h3 : (clear (4 : Fin 18)).Executes g
      (state N G.bits M E (List.replicate U.card true) I) (state N G.bits M E [] I) (U.card+1) := by
    convert clear_executes g (4 : Fin 18) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h4 : (clear (5 : Fin 18)).Executes g (state N G.bits M E [] I)
      (state N G.bits M E [] []) (I.length+1) := by
    convert clear_executes g (5 : Fin 18) _ using 1
    funext r;fin_cases r <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  unfold timeBound
  dsimp only [I] at *
  omega

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (MaskEnumeration.on_queryFree _)
  (seq_queryFree _ _ (InducedGraphEmitter.on_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))

end HiddenCircuits.Approximation.Initialization.ResidualGraphProgram
