import HiddenCircuits.Complexity.GraphVerifier.UnpairProgram

/-! Read-only indexed bit lookup with restored input and index stacks. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Lookup

def machine : OracleMachine where
  stackCount := 5
  labelCount := 19
  input := 0
  output := 2
  start := 0
  code q :=
    if q=0 then .pop 1 7 1 2
    else if q=1 then .push 4 false 3
    else if q=2 then .push 4 true 3
    else if q=3 then .pop 0 0 4 5
    else if q=4 then .push 3 false 0
    else if q=5 then .push 3 true 0
    else if q=7 then .pop 0 12 8 10
    else if q=8 then .push 0 false 9
    else if q=9 then .push 2 false 12
    else if q=10 then .push 0 true 11
    else if q=11 then .push 2 true 12
    else if q=12 then .pop 3 15 13 14
    else if q=13 then .push 0 false 12
    else if q=14 then .push 0 true 12
    else if q=15 then .pop 4 18 16 17
    else if q=16 then .push 1 false 15
    else if q=17 then .push 1 true 15
    else .halt

def config (q : Fin 19) (data index output td ti : BitString) : machine.Config :=
  ⟨q,Fin.cases data (Fin.cases index (Fin.cases output (Fin.cases td (fun _ => ti))))⟩

private theorem pop_index_nil (g : BitString → ℕ) (d o td ti : BitString) :
    machine.step g (config 0 d [] o td ti)=some (config 7 d [] o td ti,1) := by
  apply congrArg (fun c : machine.Config => some (c,1)); apply OracleConfig.ext
  · rfl
  · intro i; fin_cases i <;> rfl
private theorem pop_index (g : BitString → ℕ) (b : Bool) (d i o td ti : BitString) :
    machine.step g (config 0 d (b::i) o td ti)=some (config (if b then 2 else 1) d i o td ti,1) := by
  cases b <;> apply congrArg (fun c : machine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro j;fin_cases j <;> rfl)
private theorem push_index (g : BitString → ℕ) (b : Bool) (d i o td ti : BitString) :
    machine.step g (config (if b then 2 else 1) d i o td ti)=some (config 3 d i o td (b::ti),1) := by
  cases b <;> apply congrArg (fun c : machine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro j;fin_cases j <;> rfl)
private theorem pop_data_nil (g : BitString → ℕ) (i o td ti : BitString) :
    machine.step g (config 3 [] i o td ti)=some (config 0 [] i o td ti,1) := rfl
private theorem pop_data (g : BitString → ℕ) (b : Bool) (d i o td ti : BitString) :
    machine.step g (config 3 (b::d) i o td ti)=some (config (if b then 5 else 4) d i o td ti,1) := by
  cases b <;> apply congrArg (fun c : machine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro j;fin_cases j <;> rfl)
private theorem push_data (g : BitString → ℕ) (b : Bool) (d i o td ti : BitString) :
    machine.step g (config (if b then 5 else 4) d i o td ti)=some (config 0 d i o (b::td) ti,1) := by
  cases b <;> apply congrArg (fun c : machine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro j;fin_cases j <;> rfl)

theorem scan_steps (g : BitString → ℕ) (d i o td ti : BitString) :
    machine.Steps g (config 0 d i o td ti)
      (config 7 (d.drop i.length) [] o ((d.take i.length).reverse++td) (i.reverse++ti))
      (3*i.length+min d.length i.length+1) := by
  induction i generalizing d td ti with
  | nil => simpa using OracleMachine.Steps.single (pop_index_nil g d o td ti)
  | cons b i ih =>
    have h1 := OracleMachine.Steps.single (pop_index g b d i o td ti)
    have h2 := OracleMachine.Steps.single (push_index g b d i o td ti)
    cases d with
    | nil =>
      have h := h1.trans (h2.trans ((OracleMachine.Steps.single (pop_data_nil g i o td (b::ti))).trans
        (ih [] td (b::ti))))
      convert h using 1 <;> simp [List.reverse_cons,List.append_assoc] <;> omega
    | cons c d =>
      have h := h1.trans (h2.trans ((OracleMachine.Steps.single (pop_data g c d i o td (b::ti))).trans
        ((OracleMachine.Steps.single (push_data g c d i o td (b::ti))).trans
          (ih d (c::td) (b::ti)))))
      convert h using 1 <;> simp [List.reverse_cons,List.append_assoc,List.take_succ_cons,List.drop_succ_cons] <;> omega

private theorem inspect_nil (g : BitString → ℕ) (i o td ti : BitString) :
    machine.step g (config 7 [] i o td ti)=some (config 12 [] i o td ti,1) := rfl
private theorem inspect_pop (g : BitString → ℕ) (b : Bool) (d i o td ti : BitString) :
    machine.step g (config 7 (b::d) i o td ti)=some (config (if b then 10 else 8) d i o td ti,1) := by
  cases b <;> apply congrArg (fun c : machine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro j;fin_cases j <;> rfl)
private theorem inspect_restore (g : BitString → ℕ) (b : Bool) (d i o td ti : BitString) :
    machine.step g (config (if b then 10 else 8) d i o td ti)=some (config (if b then 11 else 9) (b::d) i o td ti,1) := by
  cases b <;> apply congrArg (fun c : machine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro j;fin_cases j <;> rfl)
private theorem inspect_output (g : BitString → ℕ) (b : Bool) (d i o td ti : BitString) :
    machine.step g (config (if b then 11 else 9) d i o td ti)=some (config 12 d i (b::o) td ti,1) := by
  cases b <;> apply congrArg (fun c : machine.Config => some (c,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro j;fin_cases j <;> rfl)

def headCost : BitString → ℕ | [] => 1 | _::_ => 3

theorem inspect_steps (g : BitString → ℕ) (d i o td ti : BitString) :
    machine.Steps g (config 7 d i o td ti)
      (config 12 d i (d.take 1++o) td ti) (headCost d) := by
  cases d with
  | nil => exact OracleMachine.Steps.single (inspect_nil g i o td ti)
  | cons b d =>
    exact (OracleMachine.Steps.single (inspect_pop g b d i o td ti)).trans
      ((OracleMachine.Steps.single (inspect_restore g b d i o td ti)).trans
        (OracleMachine.Steps.single (inspect_output g b (b::d) i o td ti)))


open BitPrograms

def dataStack : Fin 2 ↪ Fin 5 where
  toFun i := if i=0 then 3 else 0
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def dataLabel (q : Fin 4) : Fin 19 := ⟨12+q.val,by omega⟩

theorem dataEmbeds : OracleMachine.EmbedsCode reverseMachine machine dataStack dataLabel := by
  intro q h
  fin_cases q <;> simp [reverseMachine,machine,dataStack,dataLabel,OracleInstr.map] at *

theorem restore_data_steps (g : BitString → ℕ) (d i o td ti : BitString) :
    machine.Steps g (config 12 d i o td ti) (config 15 (td.reverse++d) i o [] ti) (2*td.length+1) := by
  have hc : OracleMachine.Corresponds reverseMachine machine dataStack dataLabel
      (reverseConfig 0 td d) (config 12 d i o td ti) := by
    constructor
    · rfl
    · intro j;fin_cases j <;> rfl
  obtain ⟨c,he,hcor,hframe⟩ := OracleMachine.steps_embed_frame reverseMachine machine
    dataStack dataLabel dataEmbeds g hc (BitPrograms.reverse_steps g td d)
  have hh : c=config 15 (td.reverse++d) i o [] ti := by
    apply OracleConfig.ext
    · exact hcor.1
    · intro j
      fin_cases j
      · exact hcor.2 ⟨1,by decide⟩
      · exact hframe ⟨1,by decide⟩ (by intro k;fin_cases k <;> decide)
      · exact hframe ⟨2,by decide⟩ (by intro k;fin_cases k <;> decide)
      · exact hcor.2 ⟨0,by decide⟩
      · exact hframe ⟨4,by decide⟩ (by intro k;fin_cases k <;> decide)
  rwa [hh] at he

def indexStack : Fin 2 ↪ Fin 5 where
  toFun i := if i=0 then 4 else 1
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def indexLabel (q : Fin 4) : Fin 19 := ⟨15+q.val,by omega⟩

theorem indexEmbeds : OracleMachine.EmbedsCode reverseMachine machine indexStack indexLabel := by
  intro q h
  fin_cases q <;> simp [reverseMachine,machine,indexStack,indexLabel,OracleInstr.map] at *

theorem restore_index_steps (g : BitString → ℕ) (d i o td ti : BitString) :
    machine.Steps g (config 15 d i o td ti) (config 18 d (ti.reverse++i) o td []) (2*ti.length+1) := by
  have hc : OracleMachine.Corresponds reverseMachine machine indexStack indexLabel
      (reverseConfig 0 ti i) (config 15 d i o td ti) := by
    constructor
    · rfl
    · intro j;fin_cases j <;> rfl
  obtain ⟨c,he,hcor,hframe⟩ := OracleMachine.steps_embed_frame reverseMachine machine
    indexStack indexLabel indexEmbeds g hc (BitPrograms.reverse_steps g ti i)
  have hh : c=config 18 d (ti.reverse++i) o td [] := by
    apply OracleConfig.ext
    · exact hcor.1
    · intro j
      fin_cases j
      · exact hframe ⟨0,by decide⟩ (by intro k;fin_cases k <;> decide)
      · exact hcor.2 ⟨1,by decide⟩
      · exact hframe ⟨2,by decide⟩ (by intro k;fin_cases k <;> decide)
      · exact hframe ⟨3,by decide⟩ (by intro k;fin_cases k <;> decide)
      · exact hcor.2 ⟨0,by decide⟩
  rwa [hh] at he


def cost (d i : BitString) : ℕ :=
  5*i.length+3*min d.length i.length+headCost (d.drop i.length)+3

theorem cost_bound (d i : BitString) : cost d i≤8*i.length+6 := by
  have hm := Nat.min_le_right d.length i.length
  have hh : headCost (d.drop i.length)≤3 := by cases d.drop i.length <;> simp [headCost]
  unfold cost
  omega

/-- Both read-only input stacks are restored exactly; all work cells are emptied. -/
theorem lookup_steps (g : BitString → ℕ) (d i : BitString) :
    machine.Steps g (config 0 d i [] [] [])
      (config 18 d i ((d.drop i.length).take 1) [] []) (cost d i) := by
  have h1 := scan_steps g d i [] [] []
  have h2 := inspect_steps g (d.drop i.length) [] [] ((d.take i.length).reverse++[]) (i.reverse++[])
  have h3 := restore_data_steps g (d.drop i.length) [] ((d.drop i.length).take 1++[])
    ((d.take i.length).reverse++[]) (i.reverse++[])
  have h4 := restore_index_steps g
    (((d.take i.length).reverse++[]).reverse++d.drop i.length) [] ((d.drop i.length).take 1++[]) [] (i.reverse++[])
  have hh := h1.trans (h2.trans (h3.trans h4))
  convert hh using 1 <;> simp [cost,List.take_append_drop] <;> omega

theorem lookup_runs (g : BitString → ℕ) (d i : BitString) :
    machine.Runs g (config 0 d i [] [] [])
      (config 18 d i ((d.drop i.length).take 1) [] []) (cost d i) :=
  (OracleMachine.runs_iff_steps_halt machine).mpr ⟨lookup_steps g d i,rfl⟩

theorem take_drop_lookup (d : BitString) (k : ℕ) : (d.drop k).take 1=d[k]?.toList := by
  induction d generalizing k with
  | nil => simp
  | cons b d ih =>
    cases k with
    | zero => simp
    | succ k => simpa using ih k

theorem lookup_correct (g : BitString → ℕ) (d i : BitString) :
    ∃ c : machine.Config, ∃ t : ℕ, machine.Runs g (config 0 d i [] [] []) c t ∧ t≤8*i.length+6 ∧
      c.stack (0:Fin 5)=d ∧ c.stack (1:Fin 5)=i ∧ c.stack (2:Fin 5)=d[i.length]?.toList ∧
      c.stack (3:Fin 5)=[] ∧ c.stack (4:Fin 5)=[] := by
  refine ⟨config 18 d i ((d.drop i.length).take 1) [] [],cost d i,lookup_runs g d i,cost_bound d i,
    rfl,rfl,?_,rfl,rfl⟩
  exact take_drop_lookup d i.length

end HiddenCircuits.Complexity.GraphVerifier.Lookup
