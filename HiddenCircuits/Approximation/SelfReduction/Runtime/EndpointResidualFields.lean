import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualEncoding

/-! Complete canonical-field residual emitter. Header decrement, two literal
array head removals/maps, final serialization and cleanup are all bit programs. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
open Complexity OracleBlock GraphReduction SamplerRuntime.EndpointFiber GraphVerifier.Runtime

def fieldStore (output header lows highs chosen rev : BitString) : Store 11 := fun i =>
  if i.val=0 then output else if i.val=1 then header else if i.val=2 then lows else if i.val=3 then highs
  else if i.val=4 then chosen else if i.val=11 then rev else []
def lowMap : Fin 8 ↪ Fin 12 where
  toFun i := ![2,4,5,6,7,8,9,10] i
  inj' := by decide +kernel
def highMap : Fin 8 ↪ Fin 12 where
  toFun i := ![3,4,5,6,7,8,9,10] i
  inj' := by decide +kernel
noncomputable def serializeFields : OracleBlock 11 := seq (emitWordReversed 1 11)
  (seq (emitWordReversed 2 11) (seq (emitWordReversed 3 11) (reverseOn 11 0 (by decide))))
noncomputable def fieldsProgram : OracleBlock 11 := seq (popDrop 1)
  (seq (rename deleteArray lowMap) (seq (rename deleteArray highMap) serializeFields))

lemma serializeFields_executes (g : BitString  →  ℕ) (header lows highs chosen : BitString) :
    ∃cost, serializeFields.Executes g (fieldStore [] header lows highs chosen [])
      (fieldStore (encodeBitList [header,lows,highs]) [] [] [] chosen []) cost ∧
      cost ≤ 10*(header.length+lows.length+highs.length)+50 := by
  let a := (true::pairBits header []).reverse
  let b := (true::pairBits lows []).reverse++a
  let c := (true::pairBits highs []).reverse++b
  have h1 : (emitWordReversed (1:Fin 12) 11).Executes g
      (fieldStore [] header lows highs chosen []) (fieldStore [] [] lows highs chosen a) (6*header.length+7) := by
    convert emitWordReversed_executes g (1:Fin 12) 11 (by decide)
      (fieldStore [] header lows highs chosen []) using 1
    funext i;fin_cases i <;> simp [fieldStore,a]
  have h2 : (emitWordReversed (2:Fin 12) 11).Executes g
      (fieldStore [] [] lows highs chosen a) (fieldStore [] [] [] highs chosen b) (6*lows.length+7) := by
    convert emitWordReversed_executes g (2:Fin 12) 11 (by decide)
      (fieldStore [] [] lows highs chosen a) using 1
    funext i;fin_cases i <;> rfl
  have h3 : (emitWordReversed (3:Fin 12) 11).Executes g
      (fieldStore [] [] [] highs chosen b) (fieldStore [] [] [] [] chosen c) (6*highs.length+7) := by
    convert emitWordReversed_executes g (3:Fin 12) 11 (by decide)
      (fieldStore [] [] [] highs chosen b) using 1
    funext i;fin_cases i <;> rfl
  have he : c=(encodeBitList [header,lows,highs]).reverse := by
    simp [c,b,a,encodeBitList,pairBits_eq_escaped,List.reverse_append,List.append_assoc]
  have hr : (reverseOn (11:Fin 12) 0 (by decide)).Executes g
      (fieldStore [] [] [] [] chosen c) (fieldStore (encodeBitList [header,lows,highs]) [] [] [] chosen [])
      (2*(encodeBitList [header,lows,highs]).length+1) := by
    convert reverseOn_executes g (11:Fin 12) 0 (by decide) (fieldStore [] [] [] [] chosen c) using 1
    · funext i;fin_cases i <;> simp [fieldStore,he]
    · simp [fieldStore,he]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 hr)),?_⟩
  simp [encodeBitList_length]
  omega

lemma low_executes (g : BitString  →  ℕ) (j t : ℕ) (xs : List ℕ) (N : ℕ)
    (hxs : ∀a∈xs,a ≤ N) (header highs : BitString) :
    ∃cost, (rename deleteArray lowMap).Executes g
      (fieldStore [] header (natBits (t::xs)) highs (unary j) [])
      (fieldStore [] header (natBits (xs.map (dropBoundary j))) highs (unary j) []) cost ∧
      cost ≤ 6*t+xs.length*(28*N+13*j+52)+18 := by
  obtain ⟨c,hc,hb⟩ := deleteArray_executes g j t xs N hxs
  refine ⟨c,?_,hb⟩
  apply rename_executes_to deleteArray lowMap g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim
lemma high_executes (g : BitString  →  ℕ) (j t : ℕ) (xs : List ℕ) (N : ℕ)
    (hxs : ∀a∈xs,a ≤ N) (header lows : BitString) :
    ∃cost, (rename deleteArray highMap).Executes g
      (fieldStore [] header lows (natBits (t::xs)) (unary j) [])
      (fieldStore [] header lows (natBits (xs.map (dropBoundary j))) (unary j) []) cost ∧
      cost ≤ 6*t+xs.length*(28*N+13*j+52)+18 := by
  obtain ⟨c,hc,hb⟩ := deleteArray_executes g j t xs N hxs
  refine ⟨c,?_,hb⟩
  apply rename_executes_to deleteArray highMap g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim

/-- One fixed finite emitter consumes canonical header/array fields and emits
the literal smaller canonical endpoint bytes; only the chosen-column input is
retained. The typed endpoints occur in the statement, not the instruction code. -/
theorem fieldsProgram_executes (g : BitString  →  ℕ) {n : ℕ} (E : MonotoneEndpoints (n+1))
    (j : Fin (n+1)) :
    ∃cost, fieldsProgram.Executes g
      (fieldStore [] (unary (n+1)) (encodeBitList (MonotoneEndpointEncoding.rows E.lo))
        (encodeBitList (MonotoneEndpointEncoding.rows E.hi)) (unary j.val) [])
      (fieldStore (MonotoneEndpointEncoding.encode ⟨n,deleteFirst E j⟩) [] [] [] (unary j.val) []) cost ∧
      cost ≤ 200*(n+2)^2 := by
  let lo := List.ofFn (fun i : Fin n => E.lo i.succ)
  let hi := List.ofFn (fun i : Fin n => E.hi i.succ)
  let ls := natBits (lo.map (dropBoundary j.val))
  let hs := natBits (hi.map (dropBoundary j.val))
  have hlow : encodeBitList (MonotoneEndpointEncoding.rows E.lo)=natBits (E.lo 0::lo) := by
    rw [rows_succ];rfl
  have hhigh : encodeBitList (MonotoneEndpointEncoding.rows E.hi)=natBits (E.hi 0::hi) := by
    rw [rows_succ];rfl
  have hlow' : encodeBitList (MonotoneEndpointEncoding.rows (deleteFirst E j).lo)=ls := by
    rw [residual_rows_lo];rfl
  have hhigh' : encodeBitList (MonotoneEndpointEncoding.rows (deleteFirst E j).hi)=hs := by
    rw [residual_rows_hi];rfl
  have hp : (popDrop (1:Fin 12)).Executes g
      (fieldStore [] (unary (n+1)) (natBits (E.lo 0::lo)) (natBits (E.hi 0::hi)) (unary j.val) [])
      (fieldStore [] (unary n) (natBits (E.lo 0::lo)) (natBits (E.hi 0::hi)) (unary j.val) []) 1 := by
    convert popDrop_executes (1:Fin 12) g
      (fieldStore [] (unary (n+1)) (natBits (E.lo 0::lo)) (natBits (E.hi 0::hi)) (unary j.val) []) using 1
    funext i;fin_cases i <;> simp [fieldStore,unary,List.replicate_succ]
  obtain ⟨cl,hl,hbl⟩ := low_executes g j.val (E.lo 0) lo (n+1) (endpoint_lo_bound E)
    (unary n) (natBits (E.hi 0::hi))
  obtain ⟨ch,hh,hbh⟩ := high_executes g j.val (E.hi 0) hi (n+1) (endpoint_hi_bound E) (unary n) ls
  obtain ⟨cs,hser,hbs⟩ := serializeFields_executes g (unary n) ls hs (unary j.val)
  have hexec := seq_executes _ _ g hp (seq_executes _ _ g hl (seq_executes _ _ g hh hser))
  refine ⟨1+(cl+(ch+cs+2)+2)+2,?_,?_⟩
  · simpa only [fieldsProgram,MonotoneEndpointEncoding.encode,hlow,hhigh,hlow',hhigh'] using hexec
  · have hlo := (E.lo_le_hi 0).trans (E.hi_le 0)
    have hhi := E.hi_le 0
    have hj := j.isLt
    have hsize := endpoint_array_length (deleteFirst E j)
    rw [hlow',hhigh'] at hsize
    simp only [lo,hi,List.length_ofFn,List.length_replicate] at hbl hbh hbs
    nlinarith

lemma fieldsProgram_queryFree : fieldsProgram.QueryFree := seq_queryFree _ _ (popDrop_queryFree _)
  (seq_queryFree _ _ (rename_queryFree _ _ deleteArray_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ deleteArray_queryFree)
      (seq_queryFree _ _ (emitWordReversed_queryFree _ _)
        (seq_queryFree _ _ (emitWordReversed_queryFree _ _)
          (seq_queryFree _ _ (emitWordReversed_queryFree _ _) (reverseOn_queryFree _ _ _))))))
end HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
