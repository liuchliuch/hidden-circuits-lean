import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine
import HiddenCircuits.Complexity.OracleResult

/-! A fixed bit program raises a signed binary integer to a unary exponent.
The polynomial bound accounts for every intermediate binary product. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.PowerRuntime
open OracleBlock RegisterMachine Polynomial

def registers (a b : ℤ) : Fin 7 → ℤ := fun i => if i.val=0 then a else if i.val=1 then b else 0
def instructions : List Instruction := [⟨.multiply,0,0,1⟩]
noncomputable def arithmetic : OracleBlock 15 := compile instructions
noncomputable def arithmeticTime : Polynomial ℕ := straightTime instructions

def embedding : Fin 16 ↪ Fin 17 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin 17 => q.val) h)

def state (a b : ℤ) (clock : BitString) : Store 16 := fun (i : Fin 17) =>
  if h : i.val<16 then RegisterMachine.store [] [] (signedBits ∘ registers a b) ⟨i.val,h⟩ else clock

noncomputable def body : OracleBlock 16 := rename arithmetic embedding
noncomputable def loop : OracleBlock 16 := whilePop 16 body body

theorem arithmetic_eval (a b : ℤ) : evaluate instructions (registers a b)=registers (a*b) b := by
  funext i
  fin_cases i <;> simp [instructions,evaluate,Instruction.eval,Operation.eval,registers]

theorem body_executes (oracle : BitString → ℕ) (a b : ℤ) (clock : BitString) (B : ℕ)
    (ha : (signedBits a).length≤B) (hb : (signedBits b).length≤B) :
    ∃ t, body.Executes oracle (state a b clock) (state (a*b) b clock) t ∧ t≤arithmeticTime.eval B := by
  have hR : RegisterMachine.Bounded B (registers a b) := by
    have hz : (signedBits (0:ℤ)).length≤B := by
      simp only [signedBits,List.length_cons] at ha ⊢
      change 1≤B
      omega
    intro i
    fin_cases i <;> simp only [registers] <;> first | exact ha | exact hb | exact hz
  obtain ⟨t,ht,htb⟩ := compile_polynomial instructions oracle (registers a b) B hR
    (by simp [instructions,Valid,Operation.Valid])
  rw [arithmetic_eval] at ht
  refine ⟨t,?_,htb⟩
  apply rename_executes_to arithmetic embedding oracle ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hx : i.val=16 := by
      by_contra h
      exact hi ⟨i.val,by omega⟩ (Fin.ext rfl)
    simp [state,hx]

theorem loop_executes (oracle : BitString → ℕ) (a b : ℤ) (clock : BitString) (A B : ℕ)
    (ha : a.natAbs≤2^A) (hb : b.natAbs≤2^B) :
    ∃ t, loop.Executes oracle (state a b clock) (state (a*b^clock.length) b []) t ∧
      t≤clock.length*(arithmeticTime.eval (A+B*clock.length+B+2)+2)+1 := by
  suffices ∃ t, WhileExecution (16:Fin 17) body body oracle (state a b clock)
      (state (a*b^clock.length) b []) t ∧
      t≤clock.length*(arithmeticTime.eval (A+B*clock.length+B+2)+2)+1 by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ oracle ht,hb⟩
  induction clock generalizing A a with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa only [List.length_nil,pow_zero,mul_one] using
      (WhileExecution.empty (stack := (16:Fin 17)) (B := body) (C := body) (g := oracle) (state a b []) rfl)
  | cons bit clock ih =>
    let E := A+B*(bit::clock).length+B+2
    have h₁ : (signedBits a).length≤E := (signedBits_length_of_abs_bound ha).trans (by dsimp [E];omega)
    have h₂ : (signedBits b).length≤E := (signedBits_length_of_abs_bound hb).trans (by dsimp [E];omega)
    obtain ⟨c,hc,hcb⟩ := body_executes oracle a b clock E h₁ h₂
    have hm : (a*b).natAbs≤2^(A+B) := by
      simpa only [Int.natAbs_mul,pow_add] using Nat.mul_le_mul ha hb
    obtain ⟨t,ht,htb⟩ := ih (a*b) (A+B) hm
    have he : A+B+B*clock.length+B+2=E := by dsimp [E];ring
    rw [he] at htb
    have hup : Function.update (state a b (bit::clock)) (16:Fin 17) clock=state a b clock := by
      funext i;fin_cases i <;> rfl
    have hw : WhileExecution (16:Fin 17) body body oracle (state a b (bit::clock))
        (state ((a*b)*b^clock.length) b []) (1+c+1+t) := by
      cases bit
      · exact WhileExecution.zero rfl (by rw [hup];exact hc) ht
      · exact WhileExecution.one rfl (by rw [hup];exact hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa only [List.length_cons,pow_succ,mul_assoc,mul_comm b,mul_left_comm b] using hw
    · simp only [List.length_cons]
      change 1+c+1+t≤(clock.length+1)*(arithmeticTime.eval E+2)+1
      nlinarith

theorem body_queryFree : body.QueryFree := rename_queryFree _ _ (compile_queryFree instructions)
theorem loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree


def inputStore (base clock : BitString) : Store 16 := fun (i : Fin 17) =>
  if i.val=0 then base else if i.val=1 then clock else []
def rawStore (base clock : BitString) : Store 16 := fun (i : Fin 17) =>
  if i.val=10 then base else if i.val=16 then clock else []
noncomputable def constants : OracleBlock 16 := sequence
  [push 9 true,push 9 false,push 11 false,push 12 false,push 13 false,push 14 false,push 15 false]
noncomputable def prepare : OracleBlock 16 :=
  seq (moveOn 0 10 2 (by decide) (by decide) (by decide))
    (seq (moveOn 1 16 2 (by decide) (by decide) (by decide)) constants)
noncomputable def work : OracleBlock 16 := seq prepare loop
noncomputable def program : OracleBlock 16 := seq work (cleanResult 9 2 (by decide) (by decide))
noncomputable def workTime : Polynomial ℕ := 6*X+X*(arithmeticTime.comp (X^2+X+2)+2)+39
noncomputable def time : Polynomial ℕ := 22*workTime+21*X+66

theorem constants_executes (oracle : BitString → ℕ) (b : ℤ) (clock : BitString) :
    constants.Executes oracle (rawStore (signedBits b) clock) (state 1 b clock) 22 := by
  let s0 := rawStore (signedBits b) clock
  let s1 := Function.update s0 (9:Fin 17) (true::s0 9)
  have h1 : (push (9:Fin 17) true).Executes oracle s0 s1 1 := push_executes oracle _ _ s0
  let s2 := Function.update s1 (9:Fin 17) (false::s1 9)
  have h2 : (push (9:Fin 17) false).Executes oracle s1 s2 1 := push_executes oracle _ _ s1
  let s3 := Function.update s2 (11:Fin 17) (false::s2 11)
  have h3 : (push (11:Fin 17) false).Executes oracle s2 s3 1 := push_executes oracle _ _ s2
  let s4 := Function.update s3 (12:Fin 17) (false::s3 12)
  have h4 : (push (12:Fin 17) false).Executes oracle s3 s4 1 := push_executes oracle _ _ s3
  let s5 := Function.update s4 (13:Fin 17) (false::s4 13)
  have h5 : (push (13:Fin 17) false).Executes oracle s4 s5 1 := push_executes oracle _ _ s4
  let s6 := Function.update s5 (14:Fin 17) (false::s5 14)
  have h6 : (push (14:Fin 17) false).Executes oracle s5 s6 1 := push_executes oracle _ _ s5
  let s7 := Function.update s6 (15:Fin 17) (false::s6 15)
  have h7 : (push (15:Fin 17) false).Executes oracle s6 s7 1 := push_executes oracle _ _ s6
  have he : s7=state 1 b clock := by
    funext i;fin_cases i <;> try rfl
    change [false,true]=signedBits (1:ℤ)
    decide
  have hh := seq_executes _ _ oracle h1 (seq_executes _ _ oracle h2 (seq_executes _ _ oracle h3 (seq_executes _ _ oracle h4 (seq_executes _ _ oracle h5 (seq_executes _ _ oracle h6 (seq_executes _ _ oracle h7 (skip_executes oracle s7)))))))
  rw [he] at hh
  exact hh

theorem prepare_executes (oracle : BitString → ℕ) (b : ℤ) (clock : BitString) :
    prepare.Executes oracle (inputStore (signedBits b) clock) (state 1 b clock)
      (6*((signedBits b).length+clock.length)+36) := by
  let s0 := inputStore (signedBits b) clock
  let s1 := Function.update (Function.update s0 (10:Fin 17) (signedBits b)) (0:Fin 17) []
  let s2 := rawStore (signedBits b) clock
  have h1 : (moveOn (0:Fin 17) 10 2 (by decide) (by decide) (by decide)).Executes oracle s0 s1
      (6*(signedBits b).length+5) := by
    simpa [s0,s1,inputStore] using moveOn_executes oracle (0:Fin 17) 10 2 (by decide) (by decide) (by decide) s0 rfl
  have h2 : (moveOn (1:Fin 17) 16 2 (by decide) (by decide) (by decide)).Executes oracle s1 s2
      (6*clock.length+5) := by
    convert moveOn_executes oracle (1:Fin 17) 16 2 (by decide) (by decide) (by decide) s1 rfl using 1
    funext i;fin_cases i <;> simp [s0,s1,s2,inputStore,rawStore]
  have h3 := constants_executes oracle b clock
  convert seq_executes _ _ oracle h1 (seq_executes _ _ oracle h2 h3) using 1 <;> omega

theorem work_executes (oracle : BitString → ℕ) (b : ℤ) (clock : BitString) :
    ∃ t, work.Executes oracle (inputStore (signedBits b) clock) (state (b^clock.length) b []) t ∧
      t≤workTime.eval ((signedBits b).length+clock.length) := by
  let N := (signedBits b).length+clock.length
  have hb : b.natAbs≤2^N := abs_le_pow_signed_length b N (by dsimp [N];omega)
  obtain ⟨c,hc,hcb⟩ := loop_executes oracle 1 b clock 0 N (by simp) hb
  simp only [one_mul,Nat.zero_add] at hc hcb
  have hp := prepare_executes oracle b clock
  refine ⟨6*N+36+c+2,seq_executes _ _ oracle hp hc,?_⟩
  have hclock : clock.length≤N := by dsimp [N];omega
  have hExp : N*clock.length+N+2≤N^2+N+2 := by nlinarith
  have htime := polynomial_nat_eval_mono arithmeticTime hExp
  have hm := Nat.mul_le_mul hclock (Nat.add_le_add_right htime 2)
  dsimp only at htime hm
  simp only [workTime,eval_add,eval_mul,eval_comp,eval_pow,eval_X,eval_ofNat]
  change 6*N+36+c+2≤6*N+N*(arithmeticTime.eval (N^2+N+2)+2)+39
  omega

theorem program_executes (oracle : BitString → ℕ) (b : ℤ) (clock : BitString) :
    ∃ t, program.Executes oracle (inputStore (signedBits b) clock)
      (Function.update (fun _ : Fin 17 => ([]:BitString)) 0 (signedBits (b^clock.length))) t ∧
      t≤time.eval ((signedBits b).length+clock.length) := by
  let N := (signedBits b).length+clock.length
  obtain ⟨c,hc,hcb⟩ := work_executes oracle b clock
  have hs : ∀i,(inputStore (signedBits b) clock i).length≤N := by
    intro i;unfold inputStore;split_ifs <;> dsimp [N] <;> omega
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes oracle (9:Fin 17) 2 (by decide) (by decide) (by decide)
    (state (b^clock.length) b []) (N+c) (hc.stack_bound hs)
  have hout : state (b^clock.length) b [] 9=signedBits (b^clock.length) := rfl
  rw [hout] at hd
  refine ⟨c+d+2,seq_executes _ _ oracle hc hd,?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  change c+d+2≤22*workTime.eval N+21*N+66
  change c≤workTime.eval N at hcb
  omega

theorem constants_queryFree : constants.QueryFree := by
  apply sequence_queryFree
  intro B hB
  simp at hB
  rcases hB with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact push_queryFree _ _
theorem prepare_queryFree : prepare.QueryFree := seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) constants_queryFree)
theorem program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ prepare_queryFree loop_queryFree) (cleanResult_queryFree _ _ _ _)

end HiddenCircuits.Complexity.BinaryArithmetic.PowerRuntime
