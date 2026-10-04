import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointWordQuery
import HiddenCircuits.GraphReduction.Runtime.LocalCleanup

/-! One actual graph oracle call, with query work physically cleared afterward. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointAnswerCore
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1200000

def store (input : BitString) (t s : ℕ) (answer : BitString) : Store 98 := fun i =>
  if i.val=0 then input else if i.val=1 then List.replicate t true else if i.val=2 then List.replicate s true else if i.val=3 then answer else []
def bankState (input : BitString) (t s : ℕ) (answer : BitString) (low : Store 94) : Store 98 := fun i =>
  if h:i.val<4 then store input t s answer i else low ⟨i.val-4,by omega⟩
def embedding : Fin 95 ↪ Fin 99 where
  toFun i := ⟨i.val+4,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh:=congrArg (fun z:Fin 99=>z.val) h;dsimp only at hh;omega
def cleanupPorts : List (Fin 99) := (List.finRange 99).filter (fun i=>decide (4≤ i.val))

noncomputable def before : OracleBlock 98 := seq (copyOn 0 94 4 (by decide) (by decide) (by decide))
  (seq (copyOn 1 98 4 (by decide) (by decide) (by decide))
    (seq (copyOn 2 78 4 (by decide) (by decide) (by decide)) (rename (MonotoneEndpointWordQuery.program) embedding)))
noncomputable def program : OracleBlock 98 := seq (before) (seq (query 11 3) (seq (clearList cleanupPorts) (push 3 false)))

lemma before_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c, (before).Executes g (store (wordBits w) t s [])
      (bankState (wordBits w) t s [] (MonotoneEndpointWordQuery.output w t s)) c ∧
      c≤(MonotoneEndpointWordQuery.time).eval ((wordBits w).length+t+s)+5*((wordBits w).length+t+s)+12 := by
  let start := store (wordBits w) t s []
  let a := Function.update start 94 (wordBits w)
  let b := Function.update a 98 (List.replicate t true)
  let c := Function.update b 78 (List.replicate s true)
  have h₁ : (copyOn (0:Fin 99) 94 4 (by decide) (by decide) (by decide)).Executes g start a (5*(wordBits w).length+2) := by
    simpa [a,start,store] using copyOn_executes g (0:Fin 99) 94 4 (by decide) (by decide) (by decide) start rfl
  have h₂ : (copyOn (1:Fin 99) 98 4 (by decide) (by decide) (by decide)).Executes g a b (5*t+2) := by
    simpa [b,a,start,store] using copyOn_executes g (1:Fin 99) 98 4 (by decide) (by decide) (by decide) a rfl
  have h₃ : (copyOn (2:Fin 99) 78 4 (by decide) (by decide) (by decide)).Executes g b c (5*s+2) := by
    simpa [c,b,a,start,store] using copyOn_executes g (2:Fin 99) 78 4 (by decide) (by decide) (by decide) b rfl
  obtain ⟨q,hq,hqb⟩ := MonotoneEndpointWordQuery.program_polynomial g w t s
  have hw : (rename (MonotoneEndpointWordQuery.program) embedding).Executes g c
      (bankState (wordBits w) t s [] (MonotoneEndpointWordQuery.output w t s)) q := by
    apply rename_executes_to _ embedding g hq
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have hv : i.val<4 := by
        by_contra h
        exact hi ⟨i.val-4,by omega⟩ (Fin.ext (by dsimp [embedding];omega))
      have h81:i≠94:=by intro h;subst i;norm_num at hv
      have h85:i≠98:=by intro h;subst i;norm_num at hv
      have h78:i≠78:=by intro h;subst i;norm_num at hv
      simp only [bankState,hv,if_pos,c,b,a,Function.update_of_ne h78,Function.update_of_ne h85,Function.update_of_ne h81]
      rfl
  exact ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ hw)),by omega⟩

 theorem program_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c, (program).Executes g (store (wordBits w) t s [])
      (store (wordBits w) t s (signedBits (g (MonotoneEndpointWordQuery.queryBits w t s):ℤ))) c ∧
      c≤1000*((MonotoneEndpointWordQuery.time).eval ((wordBits w).length+t+s)+((wordBits w).length+t+s)+
        (Computability.encodeNat (g (MonotoneEndpointWordQuery.queryBits w t s))).length+2) := by
  let N := (wordBits w).length+t+s
  let finish := bankState (wordBits w) t s []
    (MonotoneEndpointWordQuery.output w t s)
  let answer := Computability.encodeNat (g (MonotoneEndpointWordQuery.queryBits w t s))
  obtain ⟨a,ha,hab⟩ := before_executes g w t s
  have hin : ∀i,(store (wordBits w) t s [] i).length≤N := by
    intro i;unfold store;split_ifs <;> (try simp only [List.length_replicate,List.length_nil]) <;> dsimp [N] <;> omega
  have hs : ∀i,(finish i).length≤N+a := ha.stack_bound hin
  have hq : (query (11:Fin 99) 3).Executes g finish (Function.update finish 3 answer)
      (1+(MonotoneEndpointWordQuery.queryBits w t s).length+answer.length) := query_executes g 11 3 finish
  obtain ⟨b,hb,hbb⟩ := clearList_executes_local g cleanupPorts (Function.update finish 3 answer) (N+a) (by
    intro i hi
    have hv:4≤ i.val:=by simpa [cleanupPorts] using hi
    have h3:i≠3:=by intro h;subst i;norm_num at hv
    simpa [Function.update_of_ne h3] using hs i)
  have he : eraseStore cleanupPorts (Function.update finish 3 answer)=store (wordBits w) t s answer := by
    funext i;fin_cases i <;> simp [eraseStore,cleanupPorts,finish,bankState,store]
  rw [he] at hb
  have hp : (push (3:Fin 99) false).Executes g (store (wordBits w) t s answer)
      (store (wordBits w) t s (signedBits (g (MonotoneEndpointWordQuery.queryBits w t s):ℤ))) 1 := by
    convert push_executes g (3:Fin 99) false (store (wordBits w) t s answer) using 1
    funext i;fin_cases i <;> simp [store,answer,signedBits,negative]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hq (seq_executes _ _ g hb hp)),?_⟩
  have hg := hs 11
  have hl : cleanupPorts.length≤99 := (List.length_filter_le _ _).trans (by simp)
  have hb' := hbb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 1)
  change (MonotoneEndpointWordQuery.queryBits w t s).length≤N+a at hg
  change a≤(MonotoneEndpointWordQuery.time).eval N+5*N+12 at hab
  change a+(1+(MonotoneEndpointWordQuery.queryBits w t s).length+answer.length+(b+1+2)+2)+2≤1000*((MonotoneEndpointWordQuery.time).eval N+N+answer.length+2)
  omega
noncomputable def time : Polynomial ℕ := 1000*(MonotoneEndpointWordQuery.time+X+2)

theorem program_polynomial (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c, (program).Executes g (store (wordBits w) t s [])
      (store (wordBits w) t s (signedBits (g (MonotoneEndpointWordQuery.queryBits w t s):ℤ))) c ∧
      c ≤ (time).eval ((wordBits w).length+t+s+(signedBits (g (MonotoneEndpointWordQuery.queryBits w t s):ℤ)).length) := by
  obtain ⟨c,hc,hb⟩ := program_executes g w t s
  refine ⟨c,hc,hb.trans ?_⟩
  let N := (wordBits w).length+t+s
  let z := g (MonotoneEndpointWordQuery.queryBits w t s)
  have hm := polynomial_nat_eval_mono (MonotoneEndpointWordQuery.time) (show N ≤ N+(signedBits (z:ℤ)).length by omega)
  dsimp only at hm
  have hz : (Computability.encodeNat z).length ≤ (signedBits (z:ℤ)).length := by simp only [signedBits,List.length_cons,Int.natAbs_natCast];omega
  change 1000*((MonotoneEndpointWordQuery.time).eval N+N+(Computability.encodeNat z).length+2) ≤ _
  simp only [time,eval_mul,eval_add,eval_X,eval_ofNat]
  change _ ≤ 1000*((MonotoneEndpointWordQuery.time).eval (N+(signedBits (z:ℤ)).length)+(N+(signedBits (z:ℤ)).length)+2)
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointAnswerCore
