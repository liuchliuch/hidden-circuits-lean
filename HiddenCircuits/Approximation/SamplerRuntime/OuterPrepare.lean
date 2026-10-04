import HiddenCircuits.Approximation.SamplerRuntime.Functional
import HiddenCircuits.Complexity.GraphVerifier.BitChecks
import HiddenCircuits.Complexity.OracleMove

/-! Literal outer random-tape/sampleInput pairing, unary-precision validation,
and preserved pre-randomization input-length computation. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Outer
open Complexity Complexity.OracleBlock GraphVerifier GraphVerifier.Runtime

abbrev unary (n : ℕ) : BitString := List.replicate n true

def store (a b c d e f g h i j : BitString) : Store 44 := fun r =>
  if r.val=0 then a else if r.val=1 then b else if r.val=2 then c else if r.val=3 then d
  else if r.val=4 then e else if r.val=5 then f else if r.val=6 then g else if r.val=7 then h
  else if r.val=8 then i else if r.val=9 then j else []

def outerPorts : Fin 4 ↪ Fin 45 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 45 => z.val) h)
def lengthPorts : Fin 4 ↪ Fin 45 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 6 else if i.val=2 then 2 else 9
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def innerPorts : Fin 4 ↪ Fin 45 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 4 else if i.val=2 then 2 else 5
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def precisionPorts : Fin 1 ↪ Fin 45 := ⟨fun _ => 1,fun i j _ => Subsingleton.elim i j⟩

def allFlags : List Bool → Bool | [a,b,c] => a&&b&&c | _ => false
noncomputable def outerParse : OracleBlock 44 := unpairOn outerPorts
noncomputable def inputLength : OracleBlock 44 := headerOn lengthPorts
noncomputable def innerParse : OracleBlock 44 := unpairOn innerPorts
noncomputable def precisionCheck : OracleBlock 44 := rename (BitChecks.block true) precisionPorts
noncomputable def flagDecision : OracleBlock 44 := decision 8 [3,5,1] allFlags
noncomputable def prepare : OracleBlock 44 := seq outerParse (seq inputLength (seq (clear 9)
  (seq innerParse (seq precisionCheck flagDecision))))

def graph (raw : BitString) : BitString := (parse (parse raw).left).left
def tape (raw : BitString) : BitString := (parse raw).right
def inputSize (raw : BitString) : ℕ := (parse raw).left.length
def preValid (raw : BitString) : Bool :=
  (parse raw).ok && (parse (parse raw).left).ok && (parse (parse raw).left).right.all id

def prepared (raw : BitString) : Store 44 := store (tape raw) [] [] [] (graph raw) [] (unary (inputSize raw)) [] [preValid raw] []

lemma prepare_executes (g : BitString → ℕ) (raw : BitString) :
    ∃t,prepare.Executes g (Function.update (fun _ : Fin 45 => ([]:BitString)) 0 raw) (prepared raw) t ∧
      t≤50*(raw.length+1)^2 := by
  let r := parse raw
  let q := parse r.left
  let s0 := store raw [] [] [] [] [] [] [] [] []
  let s1 := store r.right r.left [] [r.ok] [] [] [] [] [] []
  let s2 := store r.right r.left [] [r.ok] [] [] (unary r.left.length) [] [] [r.left.all id]
  let s3 := store r.right r.left [] [r.ok] [] [] (unary r.left.length) [] [] []
  let s4 := store r.right q.right [] [r.ok] q.left [q.ok] (unary r.left.length) [] [] []
  let s5 := store r.right [q.right.all id] [] [r.ok] q.left [q.ok] (unary r.left.length) [] [] []
  have h1 : outerParse.Executes g s0 s1 (parseCost raw+2*r.left.length+1) := by
    apply unpairOn_executes outerPorts g s0 s1 raw
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim
  have h2 : inputLength.Executes g s1 s2 (5*r.left.length+3) := by
    have hh := headerOn_executes lengthPorts g s1 r.left (by funext i;fin_cases i <;> rfl)
    convert hh using 1
    funext i;fin_cases i <;> simp [s1,s2,store,lengthPorts]
  have h3 : (clear (9:Fin 45)).Executes g s2 s3 2 := by
    convert clear_executes g (9:Fin 45) s2 using 1
    funext i;fin_cases i <;> simp [s2,s3,store]
  have h4 : innerParse.Executes g s3 s4 (parseCost r.left+2*q.left.length+1) := by
    apply unpairOn_executes innerPorts g s3 s4 r.left
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim
  have h5 : precisionCheck.Executes g s4 s5 (q.right.length+2) := by
    apply rename_executes_to (BitChecks.block true) precisionPorts g (BitChecks.block_executes g true q.right)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [s5,store,precisionPorts] <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim
  let flags : Fin 45 → Bool := fun i => if i.val=3 then r.ok else if i.val=5 then q.ok else if i.val=1 then q.right.all id else false
  have h6 : flagDecision.Executes g s5 (prepared raw) 10 := by
    have hh := decision_executes (8:Fin 45) [3,5,1] (by decide) (by decide) allFlags flags g s5
      (by intro i hi;fin_cases i <;> simp_all [s5,store,flags])
    convert hh using 1
    funext i;fin_cases i <;> simp [prepared,store,eraseStore,flags,allFlags,s5,graph,tape,inputSize,preValid,r,q]
  have he : Function.update (fun _ : Fin 45 => ([]:BitString)) 0 raw=s0 := by
    funext i;fin_cases i <;> rfl
  rw [he]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6)))),?_⟩
  have hb1 := unpair_cost_bound raw
  have hb2 := unpair_cost_bound r.left
  have hl := (parse_lengths raw).1
  have hq := (parse_lengths r.left).2
  change r.left.length≤raw.length at hl
  change q.right.length≤r.left.length at hq
  change parseCost raw+2*r.left.length+1≤3*raw.length+4 at hb1
  change parseCost r.left+2*q.left.length+1≤3*r.left.length+4 at hb2
  nlinarith

lemma graph_length (raw : BitString) : (graph raw).length ≤ inputSize raw := (parse_lengths (parse raw).left).1
lemma inputSize_le (raw : BitString) : inputSize raw≤raw.length := (parse_lengths raw).1
lemma tape_length (raw : BitString) : (tape raw).length≤raw.length := (parse_lengths raw).2

lemma evaluate_eq (raw : BitString) : Functional.evaluate raw=
    if preValid raw then
      match GraphReduction.MonotoneEndpointEncoding.decode (graph raw) with
      | none => []
      | some E => Core.evaluate E.2 (inputSize raw) (tape raw)
    else [] := by
  unfold Functional.evaluate
  rw [parse_spec raw]
  cases h1 : (parse raw).ok
  · simp [h1,preValid]
  · simp only [ite_true]
    rw [parse_spec (parse raw).left]
    cases h2 : (parse (parse raw).left).ok
    · simp [h1,h2,preValid]
    · simp [h1,h2,preValid,graph,inputSize,tape] <;> rfl

lemma prepare_queryFree : prepare.QueryFree := seq_queryFree _ _ (unpairOn_queryFree _)
  (seq_queryFree _ _ (headerOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (unpairOn_queryFree _) (seq_queryFree _ _
      (rename_queryFree _ _ (BitChecks.block_queryFree _)) (decision_queryFree _ _ _)))))

end HiddenCircuits.Approximation.SamplerRuntime.Outer
