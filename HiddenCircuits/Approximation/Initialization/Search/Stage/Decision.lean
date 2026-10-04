import HiddenCircuits.Approximation.Initialization.Search.Stage.Prepare

namespace HiddenCircuits.Approximation.Initialization.Search.Stage
open Complexity Complexity.OracleBlock SamplerRuntime

theorem find_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (source : BitString) (B : ℕ) (data : BitString) (L : ℕ) (u : Fin N) (tape : BitString) :
    ∃ t,(Candidate.on candidatePorts).Executes g
      (work N G.bits (MaskEnumerationSemantics.mask U) source B data L [] u.val [] [] tape [] [])
      (work N G.bits (MaskEnumerationSemantics.mask U) source B data L [] u.val []
        (encodeOption (Candidate.result G U B tape u)) tape [] []) t ∧
      t≤Candidate.timeBound N B tape.length := by
  obtain ⟨t,ht,hb⟩ := Candidate.on_executes candidatePorts g
    (work N G.bits (MaskEnumerationSemantics.mask U) source B data L [] u.val [] [] tape [] []) G U B tape u
    (by funext r;fin_cases r <;> simp [work,candidatePorts,Candidate.state,Search.state,Candidate.params])
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext r;fin_cases r <;> simp [work,candidatePorts]

theorem commit_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (source : BitString) (B : ℕ) (π : Equiv.Perm (Fin N)) (L : ℕ) (u v : Fin N) (tape : BitString) :
    ∃ t,(PairCommit.on commitPorts).Executes g
      (work N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π) L [] u.val [] (unary v.val) tape [] [])
      (work N G.bits (MaskEnumerationSemantics.mask ((U.erase u).erase v)) source B
        (Output.witness (MonotoneEndpoints.transpose π u v)) L [] u.val [] (unary v.val) tape [] []) t ∧
      t≤100000*(N+1)^4 := by
  obtain ⟨t,ht,hb⟩ := PairCommit.on_executes commitPorts g
    (work N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π) L [] u.val [] (unary v.val) tape [] [])
    U π u v (by funext r;fin_cases r <;> simp [work,commitPorts,PairCommit.state])
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext r;fin_cases r <;> simp [work,commitPorts]

theorem choose_none (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (source : BitString) (B : ℕ) (data : BitString) (L : ℕ) (u : Fin N) (tape : BitString)
    (hn : Candidate.result G U B tape u=none) :
    ∃ t,choose.Executes g
      (work N G.bits (MaskEnumerationSemantics.mask U) source B data L [] u.val [] [] tape [] [])
      (state N G.bits (MaskEnumerationSemantics.mask U) source B data L [false]) t ∧
      t≤Candidate.timeBound N B tape.length+N+tape.length+14 := by
  obtain ⟨a,ha,hab⟩ := find_executes g G U source B data L u tape
  rw [hn] at ha
  have hf := finish_executes g N G.bits (MaskEnumerationSemantics.mask U) source B data L u.val [] tape false
  have hb := branchPop_empty (11:Fin 51) (finish false) (finish false) accepted g
    (s:=work N G.bits (MaskEnumerationSemantics.mask U) source B data L [] u.val [] [] tape [] []) rfl hf
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  have hu := u.isLt
  simp only [List.length_nil] at *
  omega

theorem choose_some (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (source : BitString) (B : ℕ) (π : Equiv.Perm (Fin N)) (L : ℕ) (u v : Fin N) (tape : BitString)
    (hv : Candidate.result G U B tape u=some v.val) :
    ∃ t,choose.Executes g
      (work N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π) L [] u.val [] [] tape [] [])
      (state N G.bits (MaskEnumerationSemantics.mask ((U.erase u).erase v)) source B
        (Output.witness (MonotoneEndpoints.transpose π u v)) L [true]) t ∧
      t≤Candidate.timeBound N B tape.length+100000*(N+1)^4+2*N+tape.length+16 := by
  obtain ⟨a,ha,hab⟩ := find_executes g G U source B (Output.witness π) L u tape
  rw [hv] at ha
  obtain ⟨c,hc,hcb⟩ := commit_executes g G U source B π L u v tape
  have hf := finish_executes g N G.bits (MaskEnumerationSemantics.mask ((U.erase u).erase v)) source B
    (Output.witness (MonotoneEndpoints.transpose π u v)) L u.val (unary v.val) tape true
  have hacc : accepted.Executes g
      (Function.update (work N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π) L [] u.val []
        (encodeOption (some v.val)) tape [] []) (11:Fin 51) (unary v.val))
      (state N G.bits (MaskEnumerationSemantics.mask ((U.erase u).erase v)) source B
        (Output.witness (MonotoneEndpoints.transpose π u v)) L [true])
      (c+(u.val+(unary v.val).length+tape.length+10)+2) := by
    convert seq_executes _ _ g hc hf using 1
    funext r;fin_cases r <;> simp [work,encodeOption]
  have hb := branchPop_true (11:Fin 51) (finish false) (finish false) accepted g rfl hacc
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  have hu := u.isLt
  have hv' := v.isLt
  simp only [List.length_replicate] at *
  omega

end HiddenCircuits.Approximation.Initialization.Search.Stage
