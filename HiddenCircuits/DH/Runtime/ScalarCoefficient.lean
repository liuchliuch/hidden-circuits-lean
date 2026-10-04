import HiddenCircuits.DH.Runtime.ScalarCoefficientArithmetic

/-! The literal crossing summand producer. Its public
inputs are three unary indices and two signed natural counts. All work is
physically cleared; neither factorials nor a cost certificate are inputs. -/
namespace HiddenCircuits.DH.Runtime.ScalarCoefficient
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
open Complexity.BinaryArithmetic.RegisterMachine Polynomial
set_option maxHeartbeats 2000000

noncomputable def copyCounts : OracleBlock 25:=seq
  (copyOn 3 22 24 (by decide) (by decide) (by decide))
  (copyOn 4 23 24 (by decide) (by decide) (by decide))
noncomputable def core : OracleBlock 25:=seq (difference 0) (seq (difference 1)
  (seq copyCounts (seq factors arithmetic)))
noncomputable def coreTime : Polynomial ℕ:=
  5*FactorialInto.time + (straightTime CrossTerm.code).comp (7*(X^2+X+3))+100*(X+1)
noncomputable def time : Polynomial ℕ:=1000*(X+coreTime+1)
def workPorts : List (Fin 26):=(List.finRange 26).filter (fun q=>6≤ q.val)
noncomputable def program : OracleBlock 25:=seq core
  (seq (moveOn 17 5 24 (by decide) (by decide) (by decide)) (clearList workPorts))

theorem core_executes (g : BitString→ ℕ) (i j r A B : ℕ) (hri:r≤ i) (hrj:r≤ j) :
    ∃t,core.Executes g (store i j r A B [])
      (state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r)
        (signedBits ∘ evaluate CrossTerm.code (CrossTerm.registers i j r A B))) t ∧
      t≤ coreTime.eval (inputSize i j r A B) := by
  obtain ⟨a,ha,hab⟩:=difference_executes g i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] 0 0 (fun _=>[]) 0 rfl
  obtain ⟨b,hb,hbb⟩:=difference_executes g i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) 0 (fun _=>[]) 1 rfl
  let s0:=state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r) (fun _=>[])
  let s1:=Function.update s0 22 (signedBits (A:ℤ))
  let s2:=state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r)
    ![[],[],[],[],[],signedBits (A:ℤ),signedBits (B:ℤ)]
  have hc0:(copyOn (3:Fin 26) 22 24 (by decide) (by decide) (by decide)).Executes g s0 s1 (5*(signedBits (A:ℤ)).length+2):=by
    convert copyOn_executes g (3:Fin 26) 22 24 (by decide) (by decide) (by decide) s0 rfl using 1
    funext q;fin_cases q <;> simp [s0,s1,state]
  have hc1:(copyOn (4:Fin 26) 23 24 (by decide) (by decide) (by decide)).Executes g s1 s2 (5*(signedBits (B:ℤ)).length+2):=by
    convert copyOn_executes g (4:Fin 26) 23 24 (by decide) (by decide) (by decide) s1 rfl using 1
    funext q;fin_cases q <;> simp [s0,s1,s2,state]
  obtain ⟨c,hc,hcb⟩:=factors_executes g i j r A B
  obtain ⟨d,hd,hdb⟩:=arithmetic_executes g i j r A B hri hrj
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb
    (seq_executes _ _ g (seq_executes _ _ g hc0 hc1) (seq_executes _ _ g hc hd))),?_⟩
  have hf:=polynomial_nat_eval_mono FactorialInto.time (show i+j+r≤ inputSize i j r A B by unfold inputSize;omega)
  have ht:=polynomial_nat_eval_mono (straightTime CrossTerm.code) (cross_input_bound i j r A B)
  simp only [coreTime,eval_add,eval_mul,eval_comp,eval_X,eval_pow,eval_ofNat,eval_one]
  simp only [eval_add,eval_mul,eval_X,eval_pow,eval_ofNat,eval_one] at ht
  dsimp only at hf ht
  unfold inputSize at *
  omega

lemma initial_bound (i j r A B : ℕ) (q : Fin 26) : (store i j r A B [] q).length≤ inputSize i j r A B:=by
  fin_cases q <;> simp [store,state,inputSize] <;> omega

/-- A fixed finite bit program evaluates the true-twin crossing coefficient. -/
theorem executes (g : BitString→ ℕ) (i j r A B : ℕ) (hri:r≤ i) (hrj:r≤ j) :
    ∃t,program.Executes g (store i j r A B [])
      (store i j r A B (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ))) t ∧
      t≤ time.eval (inputSize i j r A B) := by
  obtain ⟨c,hc,hcb⟩:=core_executes g i j r A B hri hrj
  let R:=signedBits ∘ evaluate CrossTerm.code (CrossTerm.registers i j r A B)
  let s:=state i j r (signedBits (A:ℤ)) (signedBits (B:ℤ)) [] (i-r) (j-r) R
  have hlen:∀q,(s q).length≤ inputSize i j r A B+c:=hc.stack_bound (initial_bound i j r A B)
  have hm:=moveOn_executes g (17:Fin 26) 5 24 (by decide) (by decide) (by decide) s rfl
  let s':=Function.update (Function.update s 5 (s 17++s 5)) 17 []
  have hl:∀q,(s' q).length≤ inputSize i j r A B+c+(6*(s 17).length+5):=hm.stack_bound hlen
  obtain ⟨t,ht,htb⟩:=clearList_executes g workPorts s' _ hl
  have hout:eraseStore workPorts s'=store i j r A B (signedBits (A*B*(i.choose r*j.choose r*r.factorial):ℕ)):=by
    funext q;fin_cases q <;> simp [eraseStore,workPorts,s',s,store,state,R,Function.comp_def,CrossTerm.code_result i j r A B hri hrj]
  rw [hout] at ht
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hm ht),?_⟩
  have hn:workPorts.length≤ 26:= (List.length_filter_le _ _).trans (by simp)
  have h17:=hlen 17
  have ht':t≤ 26*(inputSize i j r A B+c+(6*(s 17).length+5)+3)+1:=
    htb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [time,eval_mul,eval_add,eval_X,eval_ofNat,eval_one]
  omega

lemma core_queryFree : core.QueryFree:=seq_queryFree _ _ (difference_queryFree 0) (seq_queryFree _ _
  (difference_queryFree 1) (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (copyOn_queryFree _ _ _ _ _ _)) (seq_queryFree _ _ factors_queryFree arithmetic_queryFree)))
lemma queryFree : program.QueryFree:=seq_queryFree _ _ core_queryFree (seq_queryFree _ _
  (moveOn_queryFree _ _ _ _ _ _) (clearList_queryFree _))
end HiddenCircuits.DH.Runtime.ScalarCoefficient
