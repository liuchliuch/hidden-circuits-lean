import HiddenCircuits.Approximation.Initialization.Search.Candidate
import HiddenCircuits.Approximation.Initialization.PairCommit
import HiddenCircuits.Approximation.SelfReduction.Runtime.FirstTrue
import HiddenCircuits.Approximation.SamplerRuntime.TapeRead

/-! One actual forward extraction stage: pivot, fresh tape, finite candidate
search, pair commit, and complete private-work cleanup. -/
namespace HiddenCircuits.Approximation.Initialization.Search.Stage
open Complexity Complexity.OracleBlock

/-- Public ports 0..7 hold N, graph, mask, remaining tape, width, witness,
stage bit length, and success flag. Private ports 8..50 are cleaned. -/
def work (N : ℕ) (payload mask source : BitString) (B : ℕ) (data : BitString)
    (L : ℕ) (ok : BitString) (p : ℕ) (found selected stage clock rev : BitString) : Store 50 := fun r =>
  if r.val=0 then unary N else if r.val=1 then payload else if r.val=2 then mask
  else if r.val=3 then source else if r.val=4 then unary B else if r.val=5 then data
  else if r.val=6 then unary L else if r.val=7 then ok else if r.val=8 then unary p
  else if r.val=9 then found else if r.val=11 then selected else if r.val=12 then stage
  else if r.val=13 then clock else if r.val=14 then rev else []

def state (N : ℕ) (payload mask source : BitString) (B : ℕ) (data : BitString)
    (L : ℕ) (ok : BitString) : Store 50 := work N payload mask source B data L ok 0 [] [] [] [] []

def pivotPorts : Fin 5 ↪ Fin 51 where
  toFun r := if r.val=0 then 2 else if r.val=1 then 8 else if r.val=2 then 10
    else if r.val=3 then 9 else 14
  inj' := by decide +kernel

def tapePorts : Fin 3 ↪ Fin 51 where
  toFun r := if r.val=0 then 3 else if r.val=1 then 13 else 14
  inj' := by decide +kernel

def candidatePorts : Fin 43 ↪ Fin 51 where
  toFun r := if r.val=0 then 0 else if r.val=1 then 15 else if r.val=2 then 16
    else if r.val=3 then 11 else if r.val=4 then 17 else if r.val=5 then 18
    else if r.val=6 then 1 else if r.val=7 then 2 else if r.val=8 then 12
    else if r.val=9 then 4 else if r.val=10 then 8 else ⟨r.val+8,by omega⟩
  inj' := by decide +kernel

def commitPorts : Fin 11 ↪ Fin 51 where
  toFun r := if r.val=0 then 2 else if r.val=1 then 5 else if r.val=2 then 8
    else if r.val=3 then 11 else ⟨r.val+15,by omega⟩
  inj' := by decide +kernel

noncomputable def prepare : OracleBlock 50 :=
  seq (copyOn 6 13 18 (by decide) (by decide) (by decide))
    (seq (SamplerRuntime.TapeRead.on tapePorts) (reverseOn 14 12 (by decide)))

noncomputable def finish (ok : Bool) : OracleBlock 50 :=
  seq (clear 8) (seq (clear 11) (seq (clear 12) (push 7 ok)))

noncomputable def accepted : OracleBlock 50 := seq (PairCommit.on commitPorts) (finish true)

noncomputable def choose : OracleBlock 50 := seq (Candidate.on candidatePorts)
  (branchPop 11 (finish false) (finish false) accepted)

noncomputable def nonempty : OracleBlock 50 := seq prepare choose

noncomputable def program : OracleBlock 50 := seq (SelfReduction.Runtime.firstTrueOn pivotPorts)
  (branchPop 9 (finish true) (finish true) nonempty)

noncomputable def timeBound (N B L : ℕ) : ℕ :=
  Candidate.timeBound N B L+100000*(N+1)^4+50*(N+L+1)

theorem program_queryFree : program.QueryFree := by
  have hp : prepare.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (SamplerRuntime.TapeRead.on_queryFree _) (reverseOn_queryFree _ _ _))
  have hf : ∀ b,(finish b).QueryFree := fun b => seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ b)))
  have ha : accepted.QueryFree := seq_queryFree _ _ (PairCommit.on_queryFree _) (hf true)
  have hc : choose.QueryFree := seq_queryFree _ _ (Candidate.on_queryFree _)
    (branchPop_queryFree _ _ _ _ (hf false) (hf false) ha)
  exact seq_queryFree _ _ (rename_queryFree _ _ SelfReduction.Runtime.firstTrueMask_queryFree)
    (branchPop_queryFree _ _ _ _ (hf true) (hf true) (seq_queryFree _ _ hp hc))

end HiddenCircuits.Approximation.Initialization.Search.Stage
