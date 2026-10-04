import HiddenCircuits.GraphReduction.CliqueMatchingCount
import HiddenCircuits.Complexity.BinaryArithmetic.PowerRuntime

/-! Fresh reconstruction: odd factorial by a literal unary-clock loop of
binary multiplication and increment-by-two, followed by complete cleanup. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.OddFactorialRuntime
open Complexity OracleBlock BinaryArithmetic RegisterMachine Polynomial
set_option maxHeartbeats 900000

def registers (k : ℕ) : Fin 7 → ℤ := ![(oddFactorial k:ℤ),(2*k+1:ℕ),2,0,0,0,0]
def code : List Instruction := [⟨.multiply,0,0,1⟩,⟨.add,1,1,2⟩]
noncomputable def arithmetic : OracleBlock 15 := compile code
noncomputable def arithmeticTime : Polynomial ℕ := straightTime code
def state (k : ℕ) (clock : BitString) : Store 16 := fun i =>
  if h : i.val<16 then RegisterMachine.store [] [] (signedBits ∘ registers k) ⟨i.val,h⟩ else clock
noncomputable def body : OracleBlock 16 := rename arithmetic PowerRuntime.embedding
noncomputable def loop : OracleBlock 16 := whilePop 16 body body

def bound (n : ℕ) : ℕ := 2*n*n+2*n+4
noncomputable def boundP : Polynomial ℕ := 2*X^2+2*X+4
lemma oddFactorial_bound (n : ℕ) : oddFactorial n ≤ 2^(2*n*n) := by
  unfold oddFactorial
  calc
    _ ≤ ∏ j ∈ Finset.range n, 2^(2*n) := by
      apply Finset.prod_le_prod'
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact (show 2*j+1 ≤ 2*n by omega).trans (Nat.lt_two_pow_self.le)
    _ = _ := by simp [←pow_mul]

lemma registers_bound (k n : ℕ) (hk : k ≤ n) : Bounded (bound n) (registers k) := by
  have ha : (signedBits (oddFactorial k:ℤ)).length ≤ bound n := by
    have hb : (oddFactorial k:ℤ).natAbs ≤ 2^(2*n*n) := by
      simp only [Int.natAbs_natCast]
      exact (oddFactorial_bound k).trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
    exact (signedBits_length_of_abs_bound hb).trans (by unfold bound;omega)
  have hb : (signedBits ((2*k+1:ℕ):ℤ)).length ≤ bound n := by
    have hh : ((2*k+1:ℕ):ℤ).natAbs ≤ 2^(2*n+1) := by
      simp only [Int.natAbs_natCast]
      exact (show 2*k+1 ≤ 2*n+1 by omega).trans (Nat.lt_two_pow_self.le)
    exact (signedBits_length_of_abs_bound hh).trans (by unfold bound;omega)
  have h2 : (signedBits (2:ℤ)).length ≤ bound n := by change 3 ≤ _;unfold bound;omega
  have h0 : (signedBits (0:ℤ)).length ≤ bound n := by change 1 ≤ _;unfold bound;omega
  intro i;fin_cases i <;> first | exact ha | exact hb | exact h2 | exact h0

lemma evaluate_code (k : ℕ) : evaluate code (registers k)=registers (k+1) := by
  funext i;fin_cases i <;> simp [code,evaluate,Instruction.eval,Operation.eval,registers,oddFactorial_succ,Nat.cast_add,Nat.cast_mul] <;> ring
lemma body_executes (g : BitString → ℕ) (k n : ℕ) (clock : BitString) (hk : k ≤ n) :
    ∃c, body.Executes g (state k clock) (state (k+1) clock) c ∧ c ≤ arithmeticTime.eval (bound n) := by
  obtain ⟨c,hc,hb⟩ := compile_polynomial code g (registers k) (bound n) (registers_bound k n hk)
    (by simp [code,Valid,Operation.Valid])
  rw [evaluate_code] at hc
  refine ⟨c,?_,hb⟩
  apply rename_executes_to arithmetic PowerRuntime.embedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hv : i.val=16 := by
      by_contra hh
      exact hi ⟨i.val,by omega⟩ (Fin.ext rfl)
    simp [state,hv]

lemma loop_executes (g : BitString → ℕ) (clock : BitString) (k n : ℕ) (hk : k+clock.length ≤ n) :
    ∃c, loop.Executes g (state k clock) (state (k+clock.length) []) c ∧
      c ≤ clock.length*(arithmeticTime.eval (bound n)+2)+1 := by
  suffices ∃c, WhileExecution (16:Fin 17) body body g (state k clock) (state (k+clock.length) []) c ∧
      c ≤ clock.length*(arithmeticTime.eval (bound n)+2)+1 by
    obtain ⟨c,hc,hb⟩ := this
    exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩
  induction clock generalizing k with
  | nil => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | cons bit rest ih =>
    have hs : Function.update (state k (bit::rest)) (16:Fin 17) rest=state k rest := by
      funext i;fin_cases i <;> rfl
    obtain ⟨a,ha,hab⟩ := body_executes g k n rest (by simp only [List.length_cons] at hk;omega)
    obtain ⟨b,hb,hbb⟩ := ih (k+1) (by simp only [List.length_cons] at hk;omega)
    have hc : WhileExecution (16:Fin 17) body body g (state k (bit::rest)) (state (k+1+rest.length) []) (1+a+1+b) := by
      cases bit
      · exact WhileExecution.zero rfl (by rw [hs];exact ha) hb
      · exact WhileExecution.one rfl (by rw [hs];exact ha) hb
    refine ⟨1+a+1+b,?_,?_⟩
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc
    · simp only [List.length_cons];nlinarith

def inputStore (clock : BitString) : Store 16 := Function.update (fun _ => []) 0 clock
noncomputable def constants : OracleBlock 16 := sequence
  [push 9 true,push 9 false,push 10 true,push 10 false,push 11 true,push 11 false,push 11 false,
    push 12 false,push 13 false,push 14 false,push 15 false]
noncomputable def prepare : OracleBlock 16 := seq (reverseOn 0 16 (by decide)) constants
noncomputable def work : OracleBlock 16 := seq prepare loop
noncomputable def program : OracleBlock 16 := seq work (cleanResult 9 2 (by decide) (by decide))
noncomputable def workTime : Polynomial ℕ := 2*X+X*(arithmeticTime.comp boundP+2)+40
noncomputable def time : Polynomial ℕ := 22*workTime+21*X+66

lemma constants_executes (g : BitString → ℕ) (clock : BitString) :
    constants.Executes g (Function.update (fun _ : Fin 17 => ([]:BitString)) 16 clock) (state 0 clock) 34 := by
  let s0 : Store 16 := Function.update (fun _ => []) 16 clock
  let s1 := Function.update s0 (9:Fin 17) [true]
  let s2 := Function.update s1 (9:Fin 17) [false,true]
  let s3 := Function.update s2 (10:Fin 17) [true]
  let s4 := Function.update s3 (10:Fin 17) [false,true]
  let s5 := Function.update s4 (11:Fin 17) [true]
  let s6 := Function.update s5 (11:Fin 17) [false,true]
  let s7 := Function.update s6 (11:Fin 17) [false,false,true]
  let s8 := Function.update s7 (12:Fin 17) [false]
  let s9 := Function.update s8 (13:Fin 17) [false]
  let s10 := Function.update s9 (14:Fin 17) [false]
  let s11 := Function.update s10 (15:Fin 17) [false]
  have h1 : (push (9:Fin 17) true).Executes g s0 s1 1 := push_executes g _ _ _
  have h2 : (push (9:Fin 17) false).Executes g s1 s2 1 := push_executes g _ _ _
  have h3 : (push (10:Fin 17) true).Executes g s2 s3 1 := push_executes g _ _ _
  have h4 : (push (10:Fin 17) false).Executes g s3 s4 1 := push_executes g _ _ _
  have h5 : (push (11:Fin 17) true).Executes g s4 s5 1 := push_executes g _ _ _
  have h6 : (push (11:Fin 17) false).Executes g s5 s6 1 := push_executes g _ _ _
  have h7 : (push (11:Fin 17) false).Executes g s6 s7 1 := push_executes g _ _ _
  have h8 : (push (12:Fin 17) false).Executes g s7 s8 1 := push_executes g _ _ _
  have h9 : (push (13:Fin 17) false).Executes g s8 s9 1 := push_executes g _ _ _
  have h10 : (push (14:Fin 17) false).Executes g s9 s10 1 := push_executes g _ _ _
  have h11 : (push (15:Fin 17) false).Executes g s10 s11 1 := push_executes g _ _ _
  have he : s11=state 0 clock := by funext i;fin_cases i <;> rfl
  have hh := seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6
      (seq_executes _ _ g h7 (seq_executes _ _ g h8 (seq_executes _ _ g h9
        (seq_executes _ _ g h10 (seq_executes _ _ g h11 (skip_executes g s11)))))))))))
  rw [he] at hh
  exact hh

lemma prepare_executes (g : BitString → ℕ) (clock : BitString) :
    prepare.Executes g (inputStore clock) (state 0 clock.reverse) (2*clock.length+37) := by
  have hr : (reverseOn (0:Fin 17) 16 (by decide)).Executes g (inputStore clock)
      (Function.update (fun _ => []) 16 clock.reverse) (2*clock.length+1) := by
    convert reverseOn_executes g (0:Fin 17) 16 (by decide) (inputStore clock) using 1
    funext i;fin_cases i <;> simp [inputStore]
  convert seq_executes _ _ g hr (constants_executes g clock.reverse) using 1 <;> omega
lemma work_executes (g : BitString → ℕ) (clock : BitString) :
    ∃c, work.Executes g (inputStore clock) (state clock.length []) c ∧ c ≤ workTime.eval clock.length := by
  have hp := prepare_executes g clock
  obtain ⟨c,hc,hcb⟩ := loop_executes g clock.reverse 0 clock.length (by simp)
  simp only [List.length_reverse,Nat.zero_add] at hc hcb
  refine ⟨_,seq_executes _ _ g hp hc,?_⟩
  simp only [workTime,boundP,eval_add,eval_mul,eval_comp,eval_pow,eval_X,eval_ofNat]
  simp only [bound,pow_two,Nat.mul_assoc] at hcb ⊢
  omega

theorem program_executes (g : BitString → ℕ) (clock : BitString) :
    ∃c, program.Executes g (inputStore clock)
      (Function.update (fun _ : Fin 17 => ([]:BitString)) 0 (signedBits (oddFactorial clock.length:ℤ))) c ∧
      c ≤ time.eval clock.length := by
  obtain ⟨c,hc,hcb⟩ := work_executes g clock
  have hs : ∀i,(inputStore clock i).length ≤ clock.length := by intro i;simp [inputStore,Function.update_apply];split <;> simp_all
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes g (9:Fin 17) 2 (by decide) (by decide) (by decide)
    (state clock.length []) (clock.length+c) (hc.stack_bound hs)
  have hv : state clock.length [] 9=signedBits (oddFactorial clock.length:ℤ) := rfl
  rw [hv] at hd
  refine ⟨_,seq_executes _ _ g hc hd,?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (by
    apply sequence_queryFree;intro B hB
    simp at hB
    rcases hB with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact push_queryFree _ _))
    (whilePop_queryFree _ _ _ (rename_queryFree _ _ (compile_queryFree code)) (rename_queryFree _ _ (compile_queryFree code))))
  (cleanResult_queryFree _ _ _ _)
end HiddenCircuits.GraphReduction.Runtime.WordGraph.OddFactorialRuntime
