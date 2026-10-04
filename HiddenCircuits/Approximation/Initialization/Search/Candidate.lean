import HiddenCircuits.Approximation.Initialization.Search.Semantics
import HiddenCircuits.Approximation.Initialization.CandidateSemantics

/-! Concrete instantiation of finite search with the actual determinant callback. -/
namespace HiddenCircuits.Approximation.Initialization.Search.Candidate
open Complexity Complexity.OracleBlock

def callbackPorts : Fin 40 ↪ Fin 43 where
  toFun r := if r.val=0 then 0 else if r.val=1 then 6 else if r.val=2 then 7
    else if r.val=3 then 8 else if r.val=4 then 9 else if r.val=5 then 10
    else if r.val=6 then 1 else if r.val=7 then 2 else ⟨r.val+3,by omega⟩
  inj' := by decide +kernel

def params (payload mask tape : BitString) (B pivot : ℕ) : Store 42 := fun r =>
  if r.val=6 then payload else if r.val=7 then mask else if r.val=8 then tape
  else if r.val=9 then unary B else if r.val=10 then unary pivot else []

def predicate {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString)
    (pivot : Fin N) (i : ℕ) : Bool :=
  if hi : i<N then CandidateTest.test G U B tape pivot ⟨i,hi⟩ else false

noncomputable def callback : OracleBlock 42 := CandidateTest.on callbackPorts
noncomputable def program : OracleBlock 42 := Search.program callback

def state (N : ℕ) (payload mask tape : BitString) (B pivot : ℕ) (out : BitString) : Store 42 :=
  Search.state (params payload mask tape B pivot) N 0 [] out 0

theorem callback_spec (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (B : ℕ) (tape : BitString) (pivot : Fin N) :
    CallbackSpec callback g (params G.bits (MaskEnumerationSemantics.mask U) tape B pivot.val)
      N (predicate G U B tape pivot) (CandidateTest.timeBound N B tape.length) := by
  intro i hi m
  obtain ⟨t,ht,hb⟩ := CandidateTest.on_executes callbackPorts g
    (Search.state (params G.bits (MaskEnumerationSemantics.mask U) tape B pivot.val) N i [] [] m)
    G U B tape pivot ⟨i,hi⟩ (by
      funext r
      fin_cases r <;> simp [Search.state,params,callbackPorts,CandidateTest.state])
  refine ⟨t,?_,hb⟩
  have hp : callbackPorts 7=Search.port (k:=37) 2 := rfl
  rw [hp,Search.update_flag] at ht
  simpa only [callback,predicate,dif_pos hi] using ht

def result {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString)
    (pivot : Fin N) : Option ℕ := (List.range N).find? (predicate G U B tape pivot)

noncomputable def timeBound (N B T : ℕ) : ℕ := Search.timeBound N (CandidateTest.timeBound N B T)

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (B : ℕ) (tape : BitString) (pivot : Fin N) :
    ∃ t,program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) tape B pivot.val [])
      (state N G.bits (MaskEnumerationSemantics.mask U) tape B pivot.val
        (encodeOption (result G U B tape pivot))) t ∧ t≤timeBound N B tape.length :=
  Search.program_executes callback g (params G.bits (MaskEnumerationSemantics.mask U) tape B pivot.val)
    N (predicate G U B tape pivot) (CandidateTest.timeBound N B tape.length)
    (callback_spec g G U B tape pivot)

theorem program_queryFree : program.QueryFree :=
  Search.program_queryFree callback (CandidateTest.on_queryFree callbackPorts)

theorem result_some {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString)
    (pivot : Fin N) {i : ℕ} (h : result G U B tape pivot=some i) :
    ∃ hi : i<N, CandidateTest.test G U B tape pivot ⟨i,hi⟩=true := by
  have hi : i<N := List.mem_range.mp (List.mem_of_find?_eq_some h)
  refine ⟨hi,?_⟩
  simpa [predicate,hi] using List.find?_some h

/-- The machine's unary answer is the same first vertex as the finite-vertex search. -/
theorem result_finRange {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ)
    (tape : BitString) (pivot : Fin N) :
    result G U B tape pivot=
      ((List.finRange N).find? (CandidateTest.test G U B tape pivot)).map Fin.val := by
  unfold result
  rw [←List.map_coe_finRange_eq_range (n:=N),List.find?_map]
  congr 2
  funext v
  simp [Function.comp_def,predicate,v.isLt]

noncomputable def on {k : ℕ} (φ : Fin 43 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k N : ℕ} (φ : Fin 43 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (U : Finset (Fin N)) (B : ℕ) (tape : BitString) (pivot : Fin N)
    (hs : s∘φ=state N G.bits (MaskEnumerationSemantics.mask U) tape B pivot.val []) :
    ∃ t,(on φ).Executes g s
      (Function.update s (φ 3) (encodeOption (result G U B tape pivot))) t ∧
      t≤timeBound N B tape.length := by
  obtain ⟨t,ht,hb⟩ := program_executes g G U B tape pivot
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 3) (encodeOption (result G U B tape pivot)))∘φ=
        Function.update (s∘φ) 3 (encodeOption (result G U B tape pivot)) := by
      funext r;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    change Function.update (Search.state _ _ _ _ _ _) (Search.port 3) _=_
    exact Search.update_output _ _ _ _ _ _ _
  · intro r hr
    exact Function.update_of_ne (hr 3).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 43 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.Search.Candidate
