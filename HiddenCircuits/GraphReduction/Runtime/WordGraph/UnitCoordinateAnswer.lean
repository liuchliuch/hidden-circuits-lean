import HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitQueryAnswer
import HiddenCircuits.Complexity.CNFCloneEmitter.ClauseLookup

/-! The actual Corollary1.3 oracle receives only the interval coordinates.
The graph constructed internally is physically removed from the query packet. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitCoordinateAnswer
open Complexity OracleBlock BinaryArithmetic Polynomial
open UnitQueryAnswer (store bankState cleanupPorts)
set_option maxHeartbeats 1800000

def queryBits (w : WordInstance) (t s : ℕ) : BitString :=
  unitRepresentationBits (sampleWord w.word t) w.source w.target (2*s)
def finish (w : WordInstance) (t s : ℕ) : Store 123 := bankState (wordBits w) t s []
  (UnitWordQuery.state w t (2*s) (2*w.particles) (UnitWordQuery.graphInput w t (2*s)).1
    (UnitWordQuery.descriptor w t (2*s)) (UnitWordQuery.queryBits w t (2*s)))
def extracted (w : WordInstance) (t s : ℕ) : Store 123 :=
  Function.update (Function.update (finish w t s) 11 []) 9 (queryBits w t s)
def extractEmbedding : Fin 5 ↪ Fin 124 where
  toFun i := (![11,8,9,10,13]:Fin 5 → Fin 124) i
  inj' := by decide +kernel
noncomputable def extract : OracleBlock 123 := seq (push 8 true) (rename CNFCloneEmitter.ClauseLookup.program extractEmbedding)
noncomputable def before : OracleBlock 123 := seq UnitQueryAnswer.before extract
noncomputable def program : OracleBlock 123 := seq before (seq (query 9 3) (seq (clearList cleanupPorts) (push 3 false)))
noncomputable def beforeTime : Polynomial ℕ := 13*UnitWordQuery.time.comp (2*X)+142*X+250
noncomputable def time : Polynomial ℕ := 1000*(beforeTime+X+2)

lemma extract_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c, extract.Executes g (finish w t s) (extracted w t s) c ∧
      c≤12*(UnitWordQuery.queryBits w t (2*s)).length+32 := by
  have hp : (push (8:Fin 124) true).Executes g (finish w t s)
      (Function.update (finish w t s) 8 [true]) 1 := by
    simpa [finish,bankState,UnitWordQuery.state] using push_executes g (8:Fin 124) true (finish w t s)
  obtain ⟨c,hc,hb⟩ := CNFCloneEmitter.ClauseLookup.program_executes g
    [(UnitWordQuery.graphInput w t (2*s)).encode,queryBits w t s] 1
  have hh : (rename CNFCloneEmitter.ClauseLookup.program extractEmbedding).Executes g
      (Function.update (finish w t s) 8 [true]) (extracted w t s) c := by
    apply rename_executes_to _ extractEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · clear hc hb
      intro i hi
      have h8 : i≠8 := by intro h;subst i;exact hi 1 rfl
      have h9 : i≠9 := by intro h;subst i;exact hi 2 rfl
      have h11 : i≠11 := by intro h;subst i;exact hi 0 rfl
      simp [extracted,Function.update_of_ne h8,Function.update_of_ne h9,Function.update_of_ne h11]
  refine ⟨1+c+2,seq_executes _ _ g hp hh,?_⟩
  change c≤(1+1)*(6*(UnitWordQuery.queryBits w t (2*s)).length+14)+1 at hb
  omega

lemma before_executes (g : BitString → ℕ) (w : WordInstance) (t s : ℕ) :
    ∃c, before.Executes g (store (wordBits w) t s []) (extracted w t s) c ∧
      c≤beforeTime.eval ((wordBits w).length+t+s) := by
  obtain ⟨a,ha,hab⟩ := UnitQueryAnswer.before_executes g w t s
  obtain ⟨b,hb,hbb⟩ := extract_executes g w t s
  let N := (wordBits w).length+t+s
  have hin : ∀i,(store (wordBits w) t s [] i).length≤N := by
    intro i;unfold store;split_ifs <;> (try simp only [List.length_replicate,List.length_nil]) <;> dsimp [N] <;> omega
  have hl := ha.stack_bound hin (11:Fin 124)
  change (UnitWordQuery.queryBits w t (2*s)).length≤N+a at hl
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  change a+b+2 ≤ beforeTime.eval N
  simp only [beforeTime,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  change a≤UnitWordQuery.time.eval (2*N)+10*N+16 at hab
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
  have hs : ∀i,(extracted w t s i).length≤N+a := ha.stack_bound hin
  have hq : (query (9:Fin 124) 3).Executes g (extracted w t s) (Function.update (extracted w t s) 3 answer)
      (1+(queryBits w t s).length+answer.length) := by
    simpa only [extracted,Function.update_self] using query_executes g (9:Fin 124) 3 (extracted w t s)
  obtain ⟨b,hb,hbb⟩ := clearList_executes_local g cleanupPorts (Function.update (extracted w t s) 3 answer) (N+a) (by
    intro i hi
    have hv : 4 ≤ i.val:=by simpa [cleanupPorts] using hi
    have h3:i≠3:=by intro h;subst i;norm_num at hv
    simpa [Function.update_of_ne h3] using hs i)
  have he : eraseStore cleanupPorts (Function.update (extracted w t s) 3 answer)=store (wordBits w) t s answer := by
    funext i;fin_cases i <;> simp [eraseStore,cleanupPorts,extracted,finish,bankState,store]
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
end HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitCoordinateAnswer
