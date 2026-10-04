import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits
import HiddenCircuits.Complexity.OracleRepeat
import HiddenCircuits.Circuit.Runtime.SampleEmitterSemantics

/-! Exact signed dyadic source/sample normalization by
literal bit shifts, with a fixed seven-port program and linear execution cost. -/
namespace HiddenCircuits.Circuit.Runtime.DyadicScalar
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

def powerBits (e : ℕ) : BitString := List.replicate e false++[true]
lemma powerBits_value (e : ℕ) : value (powerBits e)=2^e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    change 0+2*value (powerBits e)=2^(e+1)
    rw [Nat.zero_add,ih,pow_succ,Nat.mul_comm]
lemma powerBits_canonical (e : ℕ) : Canonical (powerBits e) := by
  induction e with
  | zero => simp [powerBits,Canonical]
  | succ e ih =>
    change Canonical (false::powerBits e)
    exact ⟨ih,by intro h;have hh:=congrArg List.length h;simp [powerBits] at hh⟩
lemma powerBits_eq (e : ℕ) : powerBits e=Computability.encodeNat (2^e) := by
  have h:=canonical_eq_encode (powerBits_canonical e)
  rwa [powerBits_value] at h
lemma signed_powerBits (e : ℕ) : signedBits ((2:ℤ)^e)=false::powerBits e := by
  have hn : ¬(2:ℤ)^e<0 := not_lt_of_ge (pow_nonneg (by norm_num) _)
  simp [signedBits,negative,hn,Int.natAbs_pow,←powerBits_eq]

def numerator (negative : Bool) : ℤ := if negative then -1 else 1
lemma numerator_bits (negative : Bool) : signedBits (numerator negative)=[negative,true] := by cases negative <;> rfl

def store (a e : ℕ) (negative : Bool) (den num clock : BitString) : Store 6 := fun i =>
  if i.val=0 then List.replicate a true else if i.val=1 then List.replicate e true else
  if i.val=2 then [negative] else if i.val=3 then den else if i.val=4 then num else if i.val=5 then clock else []
def source (second : Bool) : Fin 7 := if second then 1 else 0
def number (second : Bool) (a e : ℕ) : ℕ := if second then e else a
noncomputable def shift (second : Bool) (factor : ℕ) : OracleBlock 6 :=
  seq (copyOn (source second) 5 6 (by cases second <;> decide) (by cases second <;> decide) (by decide))
    (repeatPrepend 5 3 (List.replicate factor false))
noncomputable def program : OracleBlock 6 :=
  seq (push 3 true) (seq (shift false 3) (seq (shift true 1)
    (seq (push 3 false) (seq (push 4 true) (copyOn 2 4 6 (by decide) (by decide) (by decide))))))
noncomputable def time : Polynomial ℕ := 20*X+40

lemma replicate_flatten (n k : ℕ) :
    (List.replicate n (List.replicate k false)).flatten=List.replicate (k*n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,List.flatten_cons,ih,←List.replicate_add]
    congr 1;ring

set_option maxHeartbeats 500000 in
lemma shift_executes (g : BitString → ℕ) (second : Bool) (factor a e : ℕ) (negative : Bool) (den num : BitString) :
    (shift second factor).Executes g (store a e negative den num [])
      (store a e negative (List.replicate (factor*number second a e) false++den) num [])
      ((3*factor+8)*number second a e+5) := by
  have hc : (copyOn (source second) (5:Fin 7) 6 (by cases second <;> decide) (by cases second <;> decide) (by decide)).Executes g
      (store a e negative den num []) (store a e negative den num (List.replicate (number second a e) true))
      (5*number second a e+2) := by
    convert copyOn_executes g (source second) (5:Fin 7) 6 (by cases second <;> decide) (by cases second <;> decide) (by decide)
      (store a e negative den num []) rfl using 1
    · funext i;cases second <;> fin_cases i <;> simp [store,source,number]
    · cases second <;> simp [store,source,number]
  have hr : (repeatPrepend (5:Fin 7) 3 (List.replicate factor false)).Executes g
      (store a e negative den num (List.replicate (number second a e) true))
      (store a e negative (List.replicate (factor*number second a e) false++den) num [])
      ((3*factor+3)*number second a e+1) := by
    convert repeatPrepend_executes g (5:Fin 7) 3 (by decide) (List.replicate factor false)
      (store a e negative den num (List.replicate (number second a e) true)) using 1
    · funext i;fin_cases i <;> simp [store,replicate_flatten,Nat.mul_comm]
    · simp [store]
  convert seq_executes _ _ g hc hr using 1 <;> ring

set_option maxHeartbeats 500000 in
theorem program_executes (g : BitString → ℕ) (a e : ℕ) (negative : Bool) :
    ∃c, program.Executes g (store a e negative [] [] [])
      (store a e negative (signedBits ((2:ℤ)^(3*a+e))) (signedBits (numerator negative)) []) c ∧
      c≤time.eval (a+e) := by
  have h0 : (push (3:Fin 7) true).Executes g (store a e negative [] [] []) (store a e negative [true] [] []) 1 := by
    convert push_executes g (3:Fin 7) true (store a e negative [] [] []) using 1
    funext i;fin_cases i <;> rfl
  have h1 := shift_executes g false 3 a e negative [true] []
  have h2 := shift_executes g true 1 a e negative (List.replicate (3*a) false++[true]) []
  simp only [number,Bool.false_eq_true,if_false,if_true] at h1 h2
  simp only [Nat.one_mul,←List.append_assoc,←List.replicate_add,Nat.add_comm e] at h2
  have h3 : (push (3:Fin 7) false).Executes g (store a e negative (powerBits (3*a+e)) [] [])
      (store a e negative (signedBits ((2:ℤ)^(3*a+e))) [] []) 1 := by
    convert push_executes g (3:Fin 7) false (store a e negative (powerBits (3*a+e)) [] []) using 1
    funext i;fin_cases i <;> simp [store,signed_powerBits]
  have h4 : (push (4:Fin 7) true).Executes g (store a e negative (signedBits ((2:ℤ)^(3*a+e))) [] [])
      (store a e negative (signedBits ((2:ℤ)^(3*a+e))) [true] []) 1 := by
    convert push_executes g (4:Fin 7) true (store a e negative (signedBits ((2:ℤ)^(3*a+e))) [] []) using 1
    funext i;fin_cases i <;> rfl
  have h5 : (copyOn (2:Fin 7) 4 6 (by decide) (by decide) (by decide)).Executes g
      (store a e negative (signedBits ((2:ℤ)^(3*a+e))) [true] [])
      (store a e negative (signedBits ((2:ℤ)^(3*a+e))) (signedBits (numerator negative)) []) 7 := by
    convert copyOn_executes g (2:Fin 7) 4 6 (by decide) (by decide) (by decide)
      (store a e negative (signedBits ((2:ℤ)^(3*a+e))) [true] []) rfl using 1
    funext i;fin_cases i <;> simp [store,numerator_bits]
  refine ⟨_,seq_executes _ _ g h0 (seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5)))),?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

lemma denominator_ne_zero (a e : ℕ) : (2:ℤ)^(3*a+e)≠0 := pow_ne_zero _ (by norm_num)
lemma normalization_identity (a e : ℕ) (negative : Bool) :
    (1/8:ℚ)^a*(SampleEmitter.signValue negative/(2:ℚ)^e)=
      (numerator negative:ℚ)/(((2:ℤ)^(3*a+e):ℤ):ℚ) := by
  have h : (1/8:ℚ)=(1/2:ℚ)^3 := by norm_num
  rw [h,←pow_mul]
  simp only [Int.cast_pow,Int.cast_ofNat,pow_add,one_div,inv_pow,div_eq_mul_inv,mul_inv_rev]
  cases negative <;> simp [numerator,SampleEmitter.signValue] <;> ring

lemma shift_queryFree (b : Bool) (factor : ℕ) : (shift b factor).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (repeatPrepend_queryFree _ _ _)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (shift_queryFree _ _) (seq_queryFree _ _ (shift_queryFree _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _) (copyOn_queryFree _ _ _ _ _ _)))))
noncomputable def on {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (a e : ℕ) (negative : Bool) (hs : s∘φ=store a e negative [] [] []) :
    ∃c,(on φ).Executes g s (Function.update (Function.update s (φ 3) (signedBits ((2:ℤ)^(3*a+e))))
      (φ 4) (signedBits (numerator negative))) c ∧ c≤time.eval (a+e) := by
  obtain ⟨c,hc,hb⟩:=program_executes g a e negative
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ g hc hs
  · funext i
    have hi:=congrFun hs i
    change s (φ i)=_ at hi
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hi]
    fin_cases i <;> rfl
  · intro i hi;simp only [Function.update_of_ne (hi 3).symm,Function.update_of_ne (hi 4).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.DyadicScalar
