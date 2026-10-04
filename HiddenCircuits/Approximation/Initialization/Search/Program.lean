import HiddenCircuits.Complexity.OracleCleanup

/-! A real finite bounded callback search, with a unary loop clock. -/
namespace HiddenCircuits.Approximation.Initialization.Search
open Complexity Complexity.OracleBlock
variable {k : ℕ}

abbrev unary (n : ℕ) : BitString := List.replicate n true

def port (i : Fin 6) : Fin (k+6) := ⟨i.val,by omega⟩

/-- Six private control stacks, with the application's fixed frame above them. -/
def state (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (remaining : ℕ) : Store (k+5) := fun r =>
  if r.val=0 then unary n else if r.val=1 then unary i else if r.val=2 then flag
  else if r.val=3 then out else if r.val=4 then unary remaining
  else if r.val=5 then [] else params r

def encodeOption : Option ℕ → BitString
  | none => []
  | some i => true :: unary i

@[simp] theorem state_port0 (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (m : ℕ) :
    state params n i flag out m (port 0)=unary n := rfl
@[simp] theorem state_port1 (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (m : ℕ) :
    state params n i flag out m (port 1)=unary i := rfl
@[simp] theorem state_port2 (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (m : ℕ) :
    state params n i flag out m (port 2)=flag := rfl
@[simp] theorem state_port3 (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (m : ℕ) :
    state params n i flag out m (port 3)=out := rfl
@[simp] theorem state_port4 (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (m : ℕ) :
    state params n i flag out m (port 4)=unary m := rfl
@[simp] theorem state_port5 (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (m : ℕ) :
    state params n i flag out m (port 5)=[] := rfl

theorem state_frame (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (m : ℕ)
    (r : Fin (k+6)) (hr : 6≤r.val) : state params n i flag out m r=params r := by
  simp [state,show r.val≠0 by omega,show r.val≠1 by omega,show r.val≠2 by omega,
    show r.val≠3 by omega,show r.val≠4 by omega,show r.val≠5 by omega]

@[simp] theorem update_index (params : Store (k+5)) (n i j : ℕ) (flag out : BitString) (m : ℕ) :
    Function.update (state params n i flag out m) (port 1) (unary j)=state params n j flag out m := by
  funext r
  simp only [state,port,Function.update_apply,Fin.ext_iff]
  split_ifs <;> simp_all

@[simp] theorem update_flag (params : Store (k+5)) (n i : ℕ) (flag flag' out : BitString) (m : ℕ) :
    Function.update (state params n i flag out m) (port 2) flag'=state params n i flag' out m := by
  funext r
  simp only [state,port,Function.update_apply,Fin.ext_iff]
  split_ifs <;> simp_all

@[simp] theorem update_output (params : Store (k+5)) (n i : ℕ) (flag out out' : BitString) (m : ℕ) :
    Function.update (state params n i flag out m) (port 3) out'=state params n i flag out' m := by
  funext r
  simp only [state,port,Function.update_apply,Fin.ext_iff]
  split_ifs <;> simp_all

@[simp] theorem update_clock (params : Store (k+5)) (n i : ℕ) (flag out : BitString) (m m' : ℕ) :
    Function.update (state params n i flag out m) (port 4) (unary m')=state params n i flag out m' := by
  funext r
  simp only [state,port,Function.update_apply,Fin.ext_iff]
  split_ifs <;> simp_all

/-- Acceptance physically copies the candidate and clears the remaining clock. -/
noncomputable def accept : OracleBlock (k+5) :=
  seq (copyOn (port 1) (port 3) (port 5) (by simp [port]) (by simp [port]) (by simp [port]))
    (seq (push (port 3) true) (clear (port 4)))

noncomputable def body (B : OracleBlock (k+5)) : OracleBlock (k+5) :=
  seq B (branchPop (port 2) (push (port 1) true) (push (port 1) true) accept)

noncomputable def loop (B : OracleBlock (k+5)) : OracleBlock (k+5) :=
  whilePop (port 4) (body B) (body B)

/-- The callback's finite code is linked into the finite search program. -/
noncomputable def program (B : OracleBlock (k+5)) : OracleBlock (k+5) :=
  seq (copyOn (port 0) (port 4) (port 5) (by simp [port]) (by simp [port]) (by simp [port]))
    (seq (loop B) (clear (port 1)))

/-- The application frame is fixed, not universally quantified. Only the index
and the remaining loop clock vary between actual callback invocations. -/
def CallbackSpec (B : OracleBlock (k+5)) (g : BitString → ℕ)
    (params : Store (k+5)) (n : ℕ) (f : ℕ → Bool) (T : ℕ) : Prop :=
  ∀ i, i<n → ∀ m, ∃ t, B.Executes g (state params n i [] [] m)
    (state params n i [f i] [] m) t ∧ t≤T

def timeBound (n T : ℕ) : ℕ := n*(T+10*n+30)+20*n+30

theorem accept_executes (g : BitString → ℕ) (params : Store (k+5)) (n i m : ℕ) :
    accept.Executes g (state params n i [] [] m)
      (state params n i [] (encodeOption (some i)) 0) (5*i+m+8) := by
  have hc : (copyOn (port 1) (port 3) (port 5) (by simp [port]) (by simp [port]) (by simp [port])).Executes g
      (state params n i [] [] m) (state params n i [] (unary i) m) (5*i+2) := by
    simpa using copyOn_executes g (port 1) (port 3) (port 5)
      (by simp [port]) (by simp [port]) (by simp [port]) (state params n i [] [] m) rfl
  have hp : (push (port 3) true).Executes g (state params n i [] (unary i) m)
      (state params n i [] (encodeOption (some i)) m) 1 := by
    simpa [encodeOption] using push_executes g (port 3) true (state params n i [] (unary i) m)
  have hd : (clear (port 4)).Executes g (state params n i [] (encodeOption (some i)) m)
      (state params n i [] (encodeOption (some i)) 0) (m+1) := by
    simpa only [state_port4,List.length_replicate,←show unary 0=[] from rfl,update_clock]
      using clear_executes g (port 4) (state params n i [] (encodeOption (some i)) m)
  convert seq_executes _ _ g hc (seq_executes _ _ g hp hd) using 1 <;> omega

theorem body_false (B : OracleBlock (k+5)) (g : BitString → ℕ) (params : Store (k+5))
    (n i m t : ℕ) (hB : B.Executes g (state params n i [] [] m) (state params n i [false] [] m) t) :
    (body B).Executes g (state params n i [] [] m) (state params n (i+1) [] [] m) (t+5) := by
  have hp : (push (port 1) true).Executes g
      (Function.update (state params n i [false] [] m) (port 2) []) (state params n (i+1) [] [] m) 1 := by
    simpa only [update_flag,state_port1,←List.replicate_succ,update_index]
      using push_executes g (port 1) true (state params n i [] [] m)
  have hb := branchPop_false (port 2) (push (port 1) true) (push (port 1) true) accept g rfl hp
  simpa [body] using seq_executes _ _ g hB hb

theorem body_true (B : OracleBlock (k+5)) (g : BitString → ℕ) (params : Store (k+5))
    (n i m t : ℕ) (hB : B.Executes g (state params n i [] [] m) (state params n i [true] [] m) t) :
    (body B).Executes g (state params n i [] [] m)
      (state params n i [] (encodeOption (some i)) 0) (t+5*i+m+12) := by
  have ha : accept.Executes g (Function.update (state params n i [true] [] m) (port 2) [])
      (state params n i [] (encodeOption (some i)) 0) (5*i+m+8) := by
    simpa only [update_flag] using accept_executes g params n i m
  have hb := branchPop_true (port 2) (push (port 1) true) (push (port 1) true) accept g rfl ha
  convert seq_executes _ _ g hB hb using 1 <;> omega

theorem program_queryFree (B : OracleBlock (k+5)) (hB : B.QueryFree) : (program B).QueryFree := by
  have ha : (accept (k:=k)).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (clear_queryFree _))
  have hb : (body B).QueryFree := seq_queryFree _ _ hB
    (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) ha)
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (whilePop_queryFree _ _ _ hb hb) (clear_queryFree _))

end HiddenCircuits.Approximation.Initialization.Search
