import HiddenCircuits.Complexity.OracleRepeat

/-! Physical bounded binary-to-unary conversion. Its exponential width bound is
used only at a logarithmic proposal width, never as unit-cost arithmetic. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.UnaryDecode
open Complexity Complexity.OracleBlock

def bit (b : Bool) : ℕ := if b then 1 else 0
def value : ℕ → BitString → ℕ
  | v,[] => v
  | v,b::bs => value (2*v+bit b) bs

def little (xs : BitString) : ℕ := value 0 xs.reverse
lemma value_append (v : ℕ) (xs ys : BitString) : value v (xs++ys)=value (value v xs) ys := by
  induction xs generalizing v <;> simp_all [value]
lemma little_nil : little []=0 := rfl
lemma little_cons (b : Bool) (xs : BitString) : little (b::xs)=2*little xs+bit b := by
  simp [little,List.reverse_cons,value_append,value]

lemma value_bound (v : ℕ) (xs : BitString) : value v xs<2^xs.length*(v+1) := by
  induction xs generalizing v with
  | nil => simp [value]
  | cons b xs ih =>
    have h := ih (2*v+bit b)
    have hb : bit b≤1 := by cases b <;> decide
    simp only [List.length_cons,pow_succ]
    have hm := Nat.mul_le_mul_left (2^xs.length) (show 2*v+bit b+1≤2*(v+1) by omega)
    change value (2*v+bit b) xs<_
    nlinarith

def state (source : BitString) (v : ℕ) (temporary scratch : BitString) : Store 3 := fun r =>
  if r.val=0 then source else if r.val=1 then List.replicate v true else if r.val=2 then temporary else scratch
noncomputable def body (b : Bool) : OracleBlock 3 := seq (copyOn 1 2 3 (by decide) (by decide) (by decide))
  (seq (reverseOn 2 1 (by decide)) (if b then push 1 true else skip))
noncomputable def program : OracleBlock 3 := whilePop 0 (body false) (body true)

lemma body_executes (g : BitString → ℕ) (xs : BitString) (v : ℕ) (b : Bool) :
    (body b).Executes g (state xs v [] []) (state xs (2*v+bit b) [] []) (7*v+8) := by
  have h1 : (copyOn (1:Fin 4) 2 3 (by decide) (by decide) (by decide)).Executes g
      (state xs v [] []) (state xs v (List.replicate v true) []) (5*v+2) := by
    convert copyOn_executes g (1:Fin 4) 2 3 (by decide) (by decide) (by decide) (state xs v [] []) rfl using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h2 : (reverseOn (2:Fin 4) 1 (by decide)).Executes g (state xs v (List.replicate v true) [])
      (state xs (2*v) [] []) (2*v+1) := by
    convert reverseOn_executes g (2:Fin 4) 1 (by decide) _ using 1
    · funext r;fin_cases r <;> simp [state,←List.replicate_add,two_mul]
    · simp [state]
  have h3 : (if b then push (1:Fin 4) true else skip).Executes g
      (state xs (2*v) [] []) (state xs (2*v+bit b) [] []) 1 := by
    cases b
    · exact skip_executes g _
    · convert push_executes g (1:Fin 4) true _ using 1
      funext r;fin_cases r <;> simp [state,bit,List.replicate_succ]
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

lemma pop_source (xs : BitString) (v : ℕ) (b : Bool) :
    Function.update (state (b::xs) v [] []) 0 xs=state xs v [] [] := by
  funext r;fin_cases r <;> rfl

/-- Every bit is physically popped, every unary doubling is copied, and the
bound accounts for the full emitted value even on arbitrary raw bitstrings. -/
theorem program_executes (g : BitString → ℕ) (xs : BitString) (v : ℕ) :
    ∃t,program.Executes g (state xs v [] []) (state [] (value v xs) [] []) t ∧
      t≤20*(xs.length+1)*2^xs.length*(v+1) := by
  suffices ∃t,WhileExecution (0:Fin 4) (body false) (body true) g
      (state xs v [] []) (state [] (value v xs) [] []) t ∧ t≤20*(xs.length+1)*2^xs.length*(v+1) by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction xs generalizing v with
  | nil => exact ⟨1,WhileExecution.empty _ rfl,by simp;omega⟩
  | cons b xs ih =>
    obtain ⟨t,ht,hb⟩ := ih (2*v+bit b)
    have hbody := body_executes g xs v b
    have hh : WhileExecution (0:Fin 4) (body false) (body true) g
        (state (b::xs) v [] []) (state [] (value (2*v+bit b) xs) [] []) (1+(7*v+8)+1+t) := by
      cases b
      · exact WhileExecution.zero rfl (by rw [pop_source];exact hbody) ht
      · exact WhileExecution.one rfl (by rw [pop_source];exact hbody) ht
    refine ⟨1+(7*v+8)+1+t,hh,?_⟩
    have hb1 : bit b≤1 := by cases b <;> decide
    have hm := Nat.mul_le_mul_left (20*(xs.length+1)*2^xs.length)
      (show 2*v+bit b+1≤2*(v+1) by omega)
    have hp : 1≤2^xs.length := Nat.one_le_pow _ _ (by decide)
    have hpv := Nat.mul_le_mul_right (v+1) hp
    simp only [List.length_cons,pow_succ]
    nlinarith

lemma body_queryFree (b : Bool) : (body b).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (by cases b <;> first | exact skip_queryFree | exact push_queryFree _ _))
lemma program_queryFree : program.QueryFree := whilePop_queryFree _ _ _ (body_queryFree false) (body_queryFree true)

end HiddenCircuits.Approximation.SamplerRuntime.UnaryDecode
