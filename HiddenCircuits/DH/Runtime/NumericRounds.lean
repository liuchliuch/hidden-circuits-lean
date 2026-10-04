import HiddenCircuits.DH.Runtime.NumericRoundsCore
import HiddenCircuits.DH.Runtime.NumericUpdate

/-! The ordinary finite machine performs a physical
unary number of exhaustive search/update rounds. No pruning plan or runtime
certificate is supplied as input. -/
namespace HiddenCircuits.DH.Runtime.NumericRounds
open Complexity OracleBlock PairCheck PruningModel Polynomial
set_option maxHeartbeats 2400000

noncomputable def update (kind : Kind) : OracleBlock 53 := NumericUpdate.on updateMap kind
noncomputable def twinDispatch : OracleBlock 53 := branchPop 51 skip (update (.twin false)) (update (.twin true))
noncomputable def dispatch : OracleBlock 53 := branchPop 51 skip (update .pendant) twinDispatch
noncomputable def round : OracleBlock 53 := seq search (seq dispatch clearIndices)
noncomputable def loop : OracleBlock 53 := whilePop 52 round round
noncomputable def program : OracleBlock 53 := seq (copyOn 5 52 53 (by decide) (by decide) (by decide)) loop
noncomputable def roundTime : Polynomial ℕ := 2400*(X+1)^5+NumericUpdate.time+2*X+20
noncomputable def time : Polynomial ℕ := 5*X+X*(roundTime+2)+5

def selected {n : ℕ} (G : MatrixData n) (s : NumericStateModel.State n) (a : Action n) (clock : BitString) : Store 53 :=
  state n G.bits (List.replicate a.keep.val true) (List.replicate a.removed.val true)
    (liveBits s.alive) (NumericEncoding.sizeBits s) (NumericEncoding.tableBits s) [] clock

lemma update_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixData n)
    (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) (a : Action n) (clock : BitString) :
    ∃t,(update a.kind).Executes g (selected G s a clock) (selected G (NumericStateModel.update s a) a clock) t ∧
      t≤NumericUpdate.time.eval n := by
  obtain ⟨t,ht,hb⟩:=NumericUpdate.on_executes updateMap g (selected G s a clock) s hs a (by
    funext q;fin_cases q <;> rfl)
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext q;fin_cases q <;> rfl

lemma dispatch_some_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixData n)
    (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) (a : Action n) (clock : BitString) :
    ∃t,dispatch.Executes g (store G s (some a) clock) (selected G (NumericStateModel.update s a) a clock) t ∧
      t≤NumericUpdate.time.eval n+4 := by
  obtain ⟨t,ht,hb⟩:=update_executes g G s hs a clock
  cases hk:a.kind with
  | pendant =>
    refine ⟨t+2,?_,by omega⟩
    apply branchPop_false (51:Fin 54) skip (update .pendant) twinDispatch g
      (rest:=[]) (by simp [store,state,resultBits,kindBits,hk])
    rw [hk] at ht
    convert ht using 1
    funext q;fin_cases q <;> simp [store,selected,state,PairSearch.keptBits,PairSearch.removedBits,resultBits,kindBits,hk]
  | twin b =>
    refine ⟨t+4,?_,by omega⟩
    have hfirst:store G s (some a) clock 51=true::[b]:=by simp [store,state,resultBits,kindBits,hk]
    have hsecond:Function.update (store G s (some a) clock) (51:Fin 54) [b] 51=b::[]:=by simp
    have he:Function.update (Function.update (store G s (some a) clock) (51:Fin 54) [b]) 51 []=selected G s a clock:=by
      funext q;fin_cases q <;> simp [store,selected,state,PairSearch.keptBits,PairSearch.removedBits,resultBits,kindBits,hk]
    rw [hk] at ht
    have hh:twinDispatch.Executes g (Function.update (store G s (some a) clock) 51 [b])
        (selected G (NumericStateModel.update s a) a clock) (t+2):=by
      cases b
      · apply branchPop_false (51:Fin 54) skip (update (.twin false)) (update (.twin true)) g hsecond
        rwa [he]
      · apply branchPop_true (51:Fin 54) skip (update (.twin false)) (update (.twin true)) g hsecond
        rwa [he]
    convert branchPop_true (51:Fin 54) skip (update .pendant) twinDispatch g hfirst hh using 1 <;> omega

lemma round_executes (g : BitString→ℕ) {n : ℕ} (G : MatrixData n)
    (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) (clock : BitString) :
    ∃t,round.Executes g (store G s none clock) (store G (NumericStateModel.rawStep G s) none clock) t ∧
      t≤roundTime.eval n := by
  obtain ⟨c,hc,hcb⟩:=search_executes g G s clock
  cases hf:PairSearch.find G s.alive with
  | none =>
    rw [hf] at hc
    have hd:dispatch.Executes g (store G s none clock) (store G s none clock) 3:=
      branchPop_empty _ _ _ _ g rfl (skip_executes g _)
    have he:clearIndices.Executes g (store G s none clock) (store G s none clock) 4:=
      clearIndices_executes g n G.bits (liveBits s.alive) (NumericEncoding.sizeBits s) (NumericEncoding.tableBits s) clock 0 0
    refine ⟨c+(3+4+2)+2,?_,?_⟩
    · simpa only [NumericStateModel.rawStep,hf] using seq_executes _ _ g hc (seq_executes _ _ g hd he)
    · simp only [roundTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one];omega
  | some a =>
    rw [hf] at hc
    obtain ⟨d,hd,hdb⟩:=dispatch_some_executes g G s hs a clock
    have he:clearIndices.Executes g (selected G (NumericStateModel.update s a) a clock)
        (store G (NumericStateModel.update s a) none clock) (a.keep.val+a.removed.val+4):=
      clearIndices_executes g n G.bits (liveBits (NumericStateModel.update s a).alive)
        (NumericEncoding.sizeBits (NumericStateModel.update s a)) (NumericEncoding.tableBits (NumericStateModel.update s a)) clock _ _
    refine ⟨c+(d+(a.keep.val+a.removed.val+4)+2)+2,?_,?_⟩
    · simpa only [NumericStateModel.rawStep,hf] using seq_executes _ _ g hc (seq_executes _ _ g hd he)
    · have hu:=a.keep.isLt;have hv:=a.removed.isLt
      simp only [roundTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one];omega

lemma loop_execution (g : BitString→ℕ) {n : ℕ} (G : MatrixData n) (fuel : ℕ)
    (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) :
    ∃t,WhileExecution 52 round round g (store G s none (List.replicate fuel true))
      (store G (NumericStateModel.rawRun G fuel s) none []) t ∧ t≤fuel*(roundTime.eval n+2)+1 := by
  induction fuel generalizing s with
  | zero => exact ⟨1,.empty _ rfl,by simp⟩
  | succ fuel ih =>
    obtain ⟨c,hc,hcb⟩:=round_executes g G s hs (List.replicate fuel true)
    obtain ⟨d,hd,hdb⟩:=ih (NumericStateModel.rawStep G s) (NumericStateModel.rawStep_safe G s hs)
    have he:Function.update (store G s none (List.replicate (fuel+1) true)) (52:Fin 54) (List.replicate fuel true)=
        store G s none (List.replicate fuel true):=by
      funext q;fin_cases q <;> simp [store,state]
    refine ⟨1+c+1+d,.one (rest:=List.replicate fuel true) (by simp [store,state,List.replicate_succ]) (by rw [he];exact hc) hd,?_⟩
    nlinarith

lemma executes (g : BitString→ℕ) {n : ℕ} (G : MatrixData n)
    (s : NumericStateModel.State n) (hs : NumericStateModel.Safe s) :
    ∃t,program.Executes g (store G s none []) (store G (NumericStateModel.rawRun G n s) none []) t ∧
      t≤time.eval n := by
  have hc:(copyOn (5:Fin 54) 52 53 (by decide) (by decide) (by decide)).Executes g
      (store G s none []) (store G s none (List.replicate n true)) (5*n+2):=by
    convert copyOn_executes g (5:Fin 54) 52 53 (by decide) (by decide) (by decide) (store G s none []) rfl using 1
    · funext q;fin_cases q <;> simp [store,state]
    · simp [store,state]
  obtain ⟨c,hc',hcb⟩:=loop_execution g G n s hs
  refine ⟨_,seq_executes _ _ g hc (whilePop_executes _ _ _ g hc'),?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat];omega

lemma update_queryFree (kind : Kind) : (update kind).QueryFree := NumericUpdate.on_queryFree _ _
lemma twinDispatch_queryFree : twinDispatch.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree (update_queryFree _) (update_queryFree _)
lemma dispatch_queryFree : dispatch.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree (update_queryFree _) twinDispatch_queryFree
lemma round_queryFree : round.QueryFree := seq_queryFree _ _ search_queryFree (seq_queryFree _ _ dispatch_queryFree clearIndices_queryFree)
lemma queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (whilePop_queryFree _ _ _ round_queryFree round_queryFree)
end HiddenCircuits.DH.Runtime.NumericRounds
