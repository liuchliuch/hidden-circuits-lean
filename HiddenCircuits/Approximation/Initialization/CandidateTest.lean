import HiddenCircuits.Approximation.Initialization.CandidateValidity
import HiddenCircuits.Approximation.Initialization.MaskPair
import HiddenCircuits.Approximation.Initialization.ResidualPositive

/-! Fully instantiated40-stack candidate callback. It performs the
actual edge/member guard, actual pair deletion, actual residual determinant,
and cleanup. The resulting bit is exactly CandidateTestData.test. -/
namespace HiddenCircuits.Approximation.Initialization.CandidateTest
open Complexity Complexity.OracleBlock

def state (N : ℕ) (payload mask tape : BitString) (B u v : ℕ)
    (out erased tmp : BitString) : Store 39 := fun r =>
  if r.val=0 then List.replicate N true else if r.val=1 then payload else if r.val=2 then mask
  else if r.val=3 then tape else if r.val=4 then List.replicate B true
  else if r.val=5 then List.replicate u true else if r.val=6 then List.replicate v true
  else if r.val=7 then out else if r.val=8 then erased else if r.val=9 then tmp else []

def validPorts : Fin 12 ↪ Fin 40 where
  toFun r := if r.val<3 then ⟨r.val,by omega⟩ else if r.val=3 then 5 else if r.val=4 then 6
    else if r.val=5 then 7 else ⟨r.val+4,by omega⟩
  inj' := by decide +kernel
def erasePorts : Fin 7 ↪ Fin 40 where
  toFun r := if r.val=0 then 2 else if r.val=1 then 5 else if r.val=2 then 6
    else if r.val=3 then 8 else ⟨r.val+6,by omega⟩
  inj' := by decide +kernel
def positivePorts : Fin 36 ↪ Fin 40 where
  toFun r := if r.val=0 then 0 else if r.val=1 then 1 else if r.val=2 then 8
    else if r.val=3 then 3 else if r.val=4 then 4 else if r.val=5 then 7
    else ⟨r.val+4,by omega⟩
  inj' := by decide +kernel

noncomputable def accepted : OracleBlock 39 := seq (MaskPair.on erasePorts)
  (seq (ResidualPositive.on positivePorts) (clear 8))
noncomputable def program : OracleBlock 39 := seq (CandidateValidity.on validPorts)
  (branchPop 7 (push 7 false) (push 7 false) accepted)

noncomputable def timeBound (N B T : ℕ) : ℕ := ResidualPositive.timeBound N B T+14*N^2+61*N+76

theorem pop_flag (N B u v : ℕ) (payload mask tape erased tmp : BitString) (b : Bool) :
    Function.update (state N payload mask tape B u v [b] erased tmp) 7 [] =
      state N payload mask tape B u v [] erased tmp := by
  funext r;fin_cases r <;> rfl

theorem accepted_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N)
    (U : Finset (Fin N)) (B : ℕ) (tape : BitString) (u v : Fin N) :
    ∃ t, accepted.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) tape B u.val v.val [] [] [])
      (state N G.bits (MaskEnumerationSemantics.mask U) tape B u.val v.val
        [ResidualPositive.positive G ((U.erase u).erase v) B tape] [] []) t ∧
      t ≤ ResidualPositive.timeBound N B tape.length+30*N+37 := by
  let M := MaskEnumerationSemantics.mask U
  let V := (U.erase u).erase v
  let E := MaskEnumerationSemantics.mask V
  obtain ⟨a,ha,hab⟩ := MaskPair.on_executes erasePorts g
    (state N G.bits M tape B u.val v.val [] [] []) U u v (by funext r;fin_cases r <;> rfl)
  have h1 : (MaskPair.on erasePorts).Executes g (state N G.bits M tape B u.val v.val [] [] [])
      (state N G.bits M tape B u.val v.val [] E []) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,erasePorts,E,V]
  obtain ⟨b,hb,hbb⟩ := ResidualPositive.on_executes positivePorts g
    (state N G.bits M tape B u.val v.val [] E []) G V B tape (by funext r;fin_cases r <;> rfl)
  have h2 : (ResidualPositive.on positivePorts).Executes g (state N G.bits M tape B u.val v.val [] E [])
      (state N G.bits M tape B u.val v.val [ResidualPositive.positive G V B tape] E []) b := by
    convert hb using 1
    funext r;fin_cases r <;> simp [state,positivePorts]
  have h3 : (clear (8 : Fin 40)).Executes g
      (state N G.bits M tape B u.val v.val [ResidualPositive.positive G V B tape] E [])
      (state N G.bits M tape B u.val v.val [ResidualPositive.positive G V B tape] [] []) (N+1) := by
    convert clear_executes g (8 : Fin 40) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state,E]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  omega

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N)
    (U : Finset (Fin N)) (B : ℕ) (tape : BitString) (u v : Fin N) :
    ∃ t, program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) tape B u.val v.val [] [] [])
      (state N G.bits (MaskEnumerationSemantics.mask U) tape B u.val v.val [test G U B tape u v] [] []) t ∧
      t ≤ timeBound N B tape.length := by
  let M := MaskEnumerationSemantics.mask U
  obtain ⟨a,ha,hab⟩ := CandidateValidity.on_executes validPorts g
    (state N G.bits M tape B u.val v.val [] [] []) G U u v (by funext r;fin_cases r <;> rfl)
  have h1 : (CandidateValidity.on validPorts).Executes g (state N G.bits M tape B u.val v.val [] [] [])
      (state N G.bits M tape B u.val v.val [valid G U u v] [] []) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,validPorts]
  have h2 : ∃ t, (branchPop (7 : Fin 40) (push 7 false) (push 7 false) accepted).Executes g
      (state N G.bits M tape B u.val v.val [valid G U u v] [] [])
      (state N G.bits M tape B u.val v.val [test G U B tape u v] [] []) t ∧
      t ≤ ResidualPositive.timeBound N B tape.length+30*N+39 := by
    by_cases hv : valid G U u v = true
    · obtain ⟨b,hb,hbb⟩ := accepted_executes g G U B tape u v
      refine ⟨b+2,?_,by omega⟩
      simp only [test,if_pos hv]
      apply branchPop_true (7 : Fin 40) _ _ _ g (rest := []) (by simp [state,hv])
      simpa only [pop_flag] using hb
    · have hf : valid G U u v = false := Bool.eq_false_iff.mpr hv
      refine ⟨3,?_,by omega⟩
      simp only [test,if_neg hv]
      apply branchPop_false (7 : Fin 40) _ _ _ g (rest := []) (by simp [state,hf])
      rw [pop_flag]
      convert push_executes g (7 : Fin 40) false _ using 1
      funext r;fin_cases r <;> rfl
  obtain ⟨b,hb,hbb⟩ := h2
  refine ⟨_,seq_executes _ _ g h1 hb,?_⟩
  unfold timeBound
  omega

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (CandidateValidity.on_queryFree _)
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _)
    (seq_queryFree _ _ (MaskPair.on_queryFree _)
      (seq_queryFree _ _ (ResidualPositive.on_queryFree _) (clear_queryFree _))))

end HiddenCircuits.Approximation.Initialization.CandidateTest
