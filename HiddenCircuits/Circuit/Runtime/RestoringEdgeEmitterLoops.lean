import HiddenCircuits.Circuit.Runtime.GateEmitterSwap

/-! Actual descending/ascending unary route loops for the restoring edge circuit.
All swap macros emit their full nine-gate canonical stream. -/
namespace HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter
open HiddenCircuits.Complexity OracleBlock

/-- Preserved lo0/d1, reverse stream2, work position3/clock4,
gate copy counter5/temp6, general copy scratch7. -/
def store (lo d position clock : ℕ) (stream counter temporary work : BitString) : Store 7 := fun i =>
  if i.val=0 then List.replicate lo true else if i.val=1 then List.replicate d true else if i.val=2 then stream
  else if i.val=3 then List.replicate position true else if i.val=4 then List.replicate clock true
  else if i.val=5 then counter else if i.val=6 then temporary else work

def gateEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := (![3,2,5,6] : Fin 4 → Fin 8) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def swap : OracleBlock 7 := rename GateEmitter.swap gateEmbedding
noncomputable def forbid : OracleBlock 7 := rename (GateEmitter.atom .forbid) gateEmbedding
noncomputable def descendBody : OracleBlock 7 := seq swap (GraphVerifier.Runtime.popDrop 3)
noncomputable def ascendBody : OracleBlock 7 := seq swap (push 3 true)
noncomputable def descend : OracleBlock 7 := whilePop 4 descendBody descendBody
noncomputable def ascend : OracleBlock 7 := whilePop 4 ascendBody ascendBody

def descendingBits (lo : ℕ) : ℕ → BitString
  | 0 => []
  | d+1 => GateEmitter.swapBits (lo+d+1) ++ descendingBits lo d

def ascendingBits : ℕ → ℕ → BitString
  | _,0 => []
  | p,d+1 => GateEmitter.swapBits p ++ ascendingBits (p+1) d

theorem swap_executes (g : BitString → ℕ) (lo d p c : ℕ) (out : BitString) :
    swap.Executes g (store lo d p c out [] [] [])
      (store lo d p c ((GateEmitter.swapBits p).reverse++out) [] [] []) (126*p+711) := by
  apply rename_executes_to _ gateEmbedding g (GateEmitter.swap_executes g p out)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim

theorem forbid_executes (g : BitString → ℕ) (lo d p c : ℕ) (out : BitString) :
    forbid.Executes g (store lo d p c out [] [] [])
      (store lo d p c ((GateEmitter.chunk .forbid p).reverse++out) [] [] []) (14*p+68) := by
  apply rename_executes_to _ gateEmbedding g (GateEmitter.atom_executes g .forbid p out)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim

theorem descendBody_executes (g : BitString → ℕ) (lo d p c : ℕ) (out : BitString) :
    descendBody.Executes g (store lo d (p+1) c out [] [] [])
      (store lo d p c ((GateEmitter.swapBits (p+1)).reverse++out) [] [] []) (126*(p+1)+714) := by
  have hs := swap_executes g lo d (p+1) c out
  have hd : (GraphVerifier.Runtime.popDrop (3:Fin 8)).Executes g
      (store lo d (p+1) c ((GateEmitter.swapBits (p+1)).reverse++out) [] [] [])
      (store lo d p c ((GateEmitter.swapBits (p+1)).reverse++out) [] [] []) 1 := by
    convert GraphVerifier.Runtime.popDrop_executes (3:Fin 8) g
      (store lo d (p+1) c ((GateEmitter.swapBits (p+1)).reverse++out) [] [] []) using 1
    funext i;fin_cases i <;> simp [store,List.replicate_succ]
  convert seq_executes _ _ g hs hd using 1 <;> omega

theorem ascendBody_executes (g : BitString → ℕ) (lo d p c : ℕ) (out : BitString) :
    ascendBody.Executes g (store lo d p c out [] [] [])
      (store lo d (p+1) c ((GateEmitter.swapBits p).reverse++out) [] [] []) (126*p+714) := by
  have hs := swap_executes g lo d p c out
  have hp : (push (3:Fin 8) true).Executes g (store lo d p c ((GateEmitter.swapBits p).reverse++out) [] [] [])
      (store lo d (p+1) c ((GateEmitter.swapBits p).reverse++out) [] [] []) 1 := by
    convert push_executes g (3:Fin 8) true (store lo d p c ((GateEmitter.swapBits p).reverse++out) [] [] []) using 1
    funext i;fin_cases i <;> simp [store,List.replicate_succ]
  convert seq_executes _ _ g hs hp using 1 <;> omega

lemma pop_clock (lo d p c : ℕ) (out : BitString) :
    Function.update (store lo d p (c+1) out [] [] []) 4 (List.replicate c true)=store lo d p c out [] [] [] := by
  funext i;fin_cases i <;> rfl

theorem descend_execution (g : BitString → ℕ) (lo d base count : ℕ) (out : BitString) :
    ∃ cost, WhileExecution (4:Fin 8) descendBody descendBody g (store lo d (base+count) count out [] [] [])
      (store lo d base 0 ((descendingBits base count).reverse++out) [] [] []) cost ∧
      cost≤count*(126*(base+count)+716)+1 := by
  induction count generalizing out with
  | zero => exact ⟨1,by simpa [descendingBits] using WhileExecution.empty (store lo d base 0 out [] [] []) rfl,by simp⟩
  | succ count ih =>
    have hb := descendBody_executes g lo d (base+count) count out
    obtain ⟨ct,ht,hbt⟩ := ih ((GateEmitter.swapBits (base+count+1)).reverse++out)
    have hbody : descendBody.Executes g
        (Function.update (store lo d (base+(count+1)) (count+1) out [] [] []) 4 (List.replicate count true))
        (store lo d (base+count) count ((GateEmitter.swapBits (base+count+1)).reverse++out) [] [] []) (126*(base+count+1)+714) := by
      rw [pop_clock]
      simpa only [Nat.add_assoc] using hb
    have h := WhileExecution.one (stack:=(4:Fin 8)) (B:=descendBody) (C:=descendBody) (g:=g) rfl hbody ht
    refine ⟨1+(126*(base+count+1)+714)+1+ct,?_,?_⟩
    · simpa [descendingBits,List.reverse_append,List.append_assoc] using h
    · nlinarith

theorem ascend_execution (g : BitString → ℕ) (lo d base count : ℕ) (out : BitString) :
    ∃ cost, WhileExecution (4:Fin 8) ascendBody ascendBody g (store lo d base count out [] [] [])
      (store lo d (base+count) 0 ((ascendingBits base count).reverse++out) [] [] []) cost ∧
      cost≤count*(126*(base+count)+716)+1 := by
  induction count generalizing base out with
  | zero => exact ⟨1,by simpa [ascendingBits] using WhileExecution.empty (store lo d base 0 out [] [] []) rfl,by simp⟩
  | succ count ih =>
    have hb := ascendBody_executes g lo d base count out
    obtain ⟨ct,ht,hbt⟩ := ih (base+1) ((GateEmitter.swapBits base).reverse++out)
    have hbody : ascendBody.Executes g
        (Function.update (store lo d base (count+1) out [] [] []) 4 (List.replicate count true))
        (store lo d (base+1) count ((GateEmitter.swapBits base).reverse++out) [] [] []) (126*base+714) := by
      rw [pop_clock];exact hb
    have h := WhileExecution.one (stack:=(4:Fin 8)) (B:=ascendBody) (C:=ascendBody) (g:=g) rfl hbody ht
    refine ⟨1+(126*base+714)+1+ct,?_,?_⟩
    · convert h using 1 <;> simp [ascendingBits,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · rw [show base+1+count=base+(count+1) by omega] at hbt
      nlinarith

theorem descend_executes (g : BitString → ℕ) (lo d base count : ℕ) (out : BitString) :
    ∃ cost, descend.Executes g (store lo d (base+count) count out [] [] [])
      (store lo d base 0 ((descendingBits base count).reverse++out) [] [] []) cost ∧
      cost≤count*(126*(base+count)+716)+1 := by
  obtain ⟨c,hc,hb⟩ := descend_execution g lo d base count out
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩

theorem ascend_executes (g : BitString → ℕ) (lo d base count : ℕ) (out : BitString) :
    ∃ cost, ascend.Executes g (store lo d base count out [] [] [])
      (store lo d (base+count) 0 ((ascendingBits base count).reverse++out) [] [] []) cost ∧
      cost≤count*(126*(base+count)+716)+1 := by
  obtain ⟨c,hc,hb⟩ := ascend_execution g lo d base count out
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩

lemma swap_queryFree : swap.QueryFree := rename_queryFree _ _ GateEmitter.swap_queryFree
lemma forbid_queryFree : forbid.QueryFree := rename_queryFree _ _ (GateEmitter.atom_queryFree _)
lemma descend_queryFree : descend.QueryFree := whilePop_queryFree _ _ _
  (seq_queryFree _ _ swap_queryFree (GraphVerifier.Runtime.popDrop_queryFree _))
  (seq_queryFree _ _ swap_queryFree (GraphVerifier.Runtime.popDrop_queryFree _))
lemma ascend_queryFree : ascend.QueryFree := whilePop_queryFree _ _ _
  (seq_queryFree _ _ swap_queryFree (push_queryFree _ _)) (seq_queryFree _ _ swap_queryFree (push_queryFree _ _))

end HiddenCircuits.Circuit.Runtime.RestoringEdgeEmitter
