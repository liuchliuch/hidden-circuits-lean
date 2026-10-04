import HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitCoordinateAnswer
import HiddenCircuits.GraphReduction.Runtime.StrictIntegerHeader

/-! Every hardness query is physically translated from a closed integer distance
header d to the strict positive radius d+1 before calling the target oracle. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.StrictIntegerAnswer
open Complexity OracleBlock BinaryArithmetic Polynomial
open UnitQueryAnswer (store cleanupPorts)
set_option maxRecDepth 2000
set_option maxHeartbeats 1600000

def queryBits (w : WordInstance) (t s : ℕ) : BitString :=
  StrictIntegerHeader.bits false (UnitCoordinateAnswer.queryBits w t s)
def queryState (w : WordInstance) (t s : ℕ) (q : BitString) : Store 123 :=
  Function.update (store (wordBits w) t s []) 9 q
def prepared (w : WordInstance) (t s : ℕ) : Store 123 := queryState w t s (queryBits w t s)
def cleanupBefore : List (Fin 124) := cleanupPorts.filter (fun i=>i≠9)
def headerMap : Fin 32 ↪ Fin 124 where
  toFun i := if i.val=0 then 9 else ⟨i.val+20,by omega⟩
  inj' := by decide +kernel
noncomputable def transform : OracleBlock 123 := rename (StrictIntegerHeader.program false) headerMap
noncomputable def before : OracleBlock 123 := seq UnitCoordinateAnswer.before
  (seq (clearList cleanupBefore) transform)
noncomputable def program : OracleBlock 123 := seq before
  (seq (query 9 3) (seq (clearList cleanupPorts) (push 3 false)))
noncomputable def beforeTime : Polynomial ℕ := 1000000*(UnitCoordinateAnswer.beforeTime+X+1)
noncomputable def time : Polynomial ℕ := 1000*(beforeTime+X+2)

lemma transform_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,transform.Executes g (queryState w t s (UnitCoordinateAnswer.queryBits w t s))
      (prepared w t s) c ∧c≤StrictIntegerHeader.time.eval (UnitCoordinateAnswer.queryBits w t s).length := by
  obtain ⟨c,hc,hb⟩ := StrictIntegerHeader.program_executes false g (UnitCoordinateAnswer.queryBits w t s)
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ headerMap g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h9 : i≠9 := by intro h;subst i;exact hi 0 rfl
    simp [prepared,queryState,Function.update_of_ne h9]

lemma before_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c,before.Executes g (store (wordBits w) t s []) (prepared w t s) c ∧
      c≤beforeTime.eval ((wordBits w).length+t+s) := by
  let N := (wordBits w).length+t+s
  obtain ⟨a,ha,hba⟩ := UnitCoordinateAnswer.before_executes g w t s
  have hin : ∀i,(store (wordBits w) t s [] i).length≤N := by
    intro i;unfold store;split_ifs <;> (try simp only [List.length_replicate,List.length_nil]) <;> dsimp [N] <;> omega
  have hs : ∀i,(UnitCoordinateAnswer.extracted w t s i).length≤N+a := ha.stack_bound hin
  obtain ⟨b,hb,hbb⟩ := clearList_executes_local g cleanupBefore (UnitCoordinateAnswer.extracted w t s) (N+a)
    (by intro i _;exact hs i)
  have he : eraseStore cleanupBefore (UnitCoordinateAnswer.extracted w t s)=
      queryState w t s (UnitCoordinateAnswer.queryBits w t s) := by
    funext i;fin_cases i <;> simp [eraseStore,cleanupBefore,cleanupPorts,UnitCoordinateAnswer.extracted,
      UnitCoordinateAnswer.finish,UnitQueryAnswer.bankState,store,queryState]
  rw [he] at hb
  obtain ⟨c,hc,hbc⟩ := transform_executes g w t s
  have hq := hs 9
  change (UnitCoordinateAnswer.queryBits w t s).length≤N+a at hq
  have hlen : cleanupBefore.length≤124 := (List.length_filter_le _ _).trans
    ((List.length_filter_le _ _).trans (by simp))
  have hbb' := hbb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  change a≤UnitCoordinateAnswer.beforeTime.eval N at hba
  simp only [StrictIntegerHeader.time,eval_mul,eval_ofNat,eval_add,eval_X,eval_one] at hbc
  change a+(b+c+2)+2≤beforeTime.eval N
  simp only [beforeTime,eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  omega

theorem program_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c, program.Executes g (store (wordBits w) t s [])
      (store (wordBits w) t s (signedBits (g (queryBits w t s):ℤ))) c ∧
      c≤1000*(beforeTime.eval ((wordBits w).length+t+s)+((wordBits w).length+t+s)+
        (Computability.encodeNat (g (queryBits w t s))).length+2) := by
  let N := (wordBits w).length+t+s
  let answer := Computability.encodeNat (g (queryBits w t s))
  obtain ⟨a,ha,hab⟩ := before_executes g w t s
  have hin : ∀i,(store (wordBits w) t s [] i).length≤N := by
    intro i;unfold store;split_ifs <;> (try simp only [List.length_replicate,List.length_nil]) <;> dsimp [N] <;> omega
  have hs : ∀i,(prepared w t s i).length≤N+a := ha.stack_bound hin
  have hq : (query (9:Fin 124) 3).Executes g (prepared w t s) (Function.update (prepared w t s) 3 answer)
      (1+(queryBits w t s).length+answer.length) := by
    simpa only [prepared,queryState,Function.update_self] using query_executes g (9:Fin 124) 3 (prepared w t s)
  obtain ⟨b,hb,hbb⟩ := clearList_executes_local g cleanupPorts (Function.update (prepared w t s) 3 answer) (N+a) (by
    intro i hi
    have hv : 4 ≤ i.val:=by simpa [cleanupPorts] using hi
    have h3:i≠3:=by intro h;subst i;norm_num at hv
    simpa [Function.update_of_ne h3] using hs i)
  have he : eraseStore cleanupPorts (Function.update (prepared w t s) 3 answer)=store (wordBits w) t s answer := by
    funext i;fin_cases i <;> simp [eraseStore,cleanupPorts,prepared,queryState,store]
  rw [he] at hb
  have hp : (push (3:Fin 124) false).Executes g (store (wordBits w) t s answer)
      (store (wordBits w) t s (signedBits (g (queryBits w t s):ℤ))) 1 := by
    convert push_executes g (3:Fin 124) false (store (wordBits w) t s answer) using 1
    funext i;fin_cases i <;> simp [store,answer,signedBits,negative]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hq (seq_executes _ _ g hb hp)),?_⟩
  have hg := hs 9
  have hl : cleanupPorts.length≤124 := (List.length_filter_le _ _).trans (by simp)
  have hb' := hbb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 1)
  change (queryBits w t s).length≤N+a at hg
  change a≤beforeTime.eval N at hab
  change a+(1+(queryBits w t s).length+answer.length+(b+1+2)+2)+2≤1000*(beforeTime.eval N+N+answer.length+2)
  omega

theorem program_polynomial (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c, program.Executes g (store (wordBits w) t s [])
      (store (wordBits w) t s (signedBits (g (queryBits w t s):ℤ))) c ∧
      c ≤ time.eval ((wordBits w).length+t+s+(signedBits (g (queryBits w t s):ℤ)).length) := by
  obtain ⟨c,hc,hb⟩ := program_executes g w t s
  refine ⟨c,hc,hb.trans ?_⟩
  let N := (wordBits w).length+t+s
  let z := g (queryBits w t s)
  have hm := polynomial_nat_eval_mono beforeTime (show N ≤ N+(signedBits (z:ℤ)).length by omega)
  dsimp only at hm
  have hz : (Computability.encodeNat z).length ≤ (signedBits (z:ℤ)).length := by simp only [signedBits,List.length_cons,Int.natAbs_natCast];omega
  change 1000*(beforeTime.eval N+N+(Computability.encodeNat z).length+2) ≤ _
  simp only [time,eval_mul,eval_add,eval_X,eval_ofNat]
  change _ ≤ 1000*(beforeTime.eval (N+(signedBits (z:ℤ)).length)+(N+(signedBits (z:ℤ)).length)+2)
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.StrictIntegerAnswer
