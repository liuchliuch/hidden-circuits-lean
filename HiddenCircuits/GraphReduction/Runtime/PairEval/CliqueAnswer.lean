import HiddenCircuits.GraphReduction.Runtime.PairEval.CliqueFrontend
import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphAnswer
import HiddenCircuits.GraphReduction.Runtime.LocalCleanup

/-! One actual graph oracle call, with query work physically cleared afterward. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.CliqueAnswer
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
set_option maxHeartbeats 1200000

open GraphAnswer (store bankState embedding cleanupPorts)
variable (kind : CliqueFrontend.Kind)

noncomputable def before : OracleBlock 85 := seq (copyOn 0 81 4 (by decide) (by decide) (by decide))
  (seq (copyOn 1 85 4 (by decide) (by decide) (by decide))
    (seq (copyOn 2 78 4 (by decide) (by decide) (by decide)) (rename (CliqueFrontend.program kind) embedding)))
noncomputable def program : OracleBlock 85 := seq (before kind) (seq (query 11 3) (seq (clearList cleanupPorts) (push 3 false)))

lemma before_executes (g : BitString → ℕ) (w : PairInput) (t s : ℕ) :
    ∃c, (before kind).Executes g (store (pairInputBits w) t s [])
      (bankState (pairInputBits w) t s [] (CliqueFrontend.output kind w t s)) c ∧
      c≤(CliqueFrontend.time kind).eval ((pairInputBits w).length+t+s)+5*((pairInputBits w).length+t+s)+12 := by
  let start := store (pairInputBits w) t s []
  let a := Function.update start 81 (pairInputBits w)
  let b := Function.update a 85 (List.replicate t true)
  let c := Function.update b 78 (List.replicate s true)
  have h₁ : (copyOn (0:Fin 86) 81 4 (by decide) (by decide) (by decide)).Executes g start a (5*(pairInputBits w).length+2) := by
    simpa [a,start,store] using copyOn_executes g (0:Fin 86) 81 4 (by decide) (by decide) (by decide) start rfl
  have h₂ : (copyOn (1:Fin 86) 85 4 (by decide) (by decide) (by decide)).Executes g a b (5*t+2) := by
    simpa [b,a,start,store] using copyOn_executes g (1:Fin 86) 85 4 (by decide) (by decide) (by decide) a rfl
  have h₃ : (copyOn (2:Fin 86) 78 4 (by decide) (by decide) (by decide)).Executes g b c (5*s+2) := by
    simpa [c,b,a,start,store] using copyOn_executes g (2:Fin 86) 78 4 (by decide) (by decide) (by decide) b rfl
  obtain ⟨q,hq,hqb⟩ := CliqueFrontend.program_executes kind g w t s
  have hw : (rename (CliqueFrontend.program kind) embedding).Executes g c
      (bankState (pairInputBits w) t s [] (CliqueFrontend.output kind w t s)) q := by
    apply rename_executes_to _ embedding g hq
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have hv : i.val<4 := by
        by_contra h
        exact hi ⟨i.val-4,by omega⟩ (Fin.ext (by dsimp [embedding];omega))
      have h81:i≠81:=by intro h;subst i;norm_num at hv
      have h85:i≠85:=by intro h;subst i;norm_num at hv
      have h78:i≠78:=by intro h;subst i;norm_num at hv
      simp only [bankState,hv,if_pos,c,b,a,Function.update_of_ne h78,Function.update_of_ne h85,Function.update_of_ne h81]
      rfl
  exact ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ hw)),by omega⟩

 theorem program_executes (g : BitString → ℕ) (w : PairInput) (t s : ℕ) :
    ∃c, (program kind).Executes g (store (pairInputBits w) t s [])
      (store (pairInputBits w) t s (signedBits (g (CliqueFrontend.queryBits kind w t s):ℤ))) c ∧
      c≤1000*((CliqueFrontend.time kind).eval ((pairInputBits w).length+t+s)+((pairInputBits w).length+t+s)+
        (Computability.encodeNat (g (CliqueFrontend.queryBits kind w t s))).length+2) := by
  let N := (pairInputBits w).length+t+s
  let finish := bankState (pairInputBits w) t s []
    (CliqueFrontend.output kind w t s)
  let answer := Computability.encodeNat (g (CliqueFrontend.queryBits kind w t s))
  obtain ⟨a,ha,hab⟩ := before_executes kind g w t s
  have hin : ∀i,(store (pairInputBits w) t s [] i).length≤N := by
    intro i;unfold store;split_ifs <;> (try simp only [List.length_replicate,List.length_nil]) <;> dsimp [N] <;> omega
  have hs : ∀i,(finish i).length≤N+a := ha.stack_bound hin
  have hq : (query (11:Fin 86) 3).Executes g finish (Function.update finish 3 answer)
      (1+(CliqueFrontend.queryBits kind w t s).length+answer.length) := query_executes g 11 3 finish
  obtain ⟨b,hb,hbb⟩ := clearList_executes_local g cleanupPorts (Function.update finish 3 answer) (N+a) (by
    intro i hi
    have hv:4≤ i.val:=by simpa [cleanupPorts] using hi
    have h3:i≠3:=by intro h;subst i;norm_num at hv
    simpa [Function.update_of_ne h3] using hs i)
  have he : eraseStore cleanupPorts (Function.update finish 3 answer)=store (pairInputBits w) t s answer := by
    funext i;fin_cases i <;> simp [eraseStore,cleanupPorts,finish,bankState,store]
  rw [he] at hb
  have hp : (push (3:Fin 86) false).Executes g (store (pairInputBits w) t s answer)
      (store (pairInputBits w) t s (signedBits (g (CliqueFrontend.queryBits kind w t s):ℤ))) 1 := by
    convert push_executes g (3:Fin 86) false (store (pairInputBits w) t s answer) using 1
    funext i;fin_cases i <;> simp [store,answer,signedBits,negative]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hq (seq_executes _ _ g hb hp)),?_⟩
  have hg := hs 11
  have hl : cleanupPorts.length≤86 := (List.length_filter_le _ _).trans (by simp)
  have hb' := hbb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 1)
  change (CliqueFrontend.queryBits kind w t s).length≤N+a at hg
  change a≤(CliqueFrontend.time kind).eval N+5*N+12 at hab
  change a+(1+(CliqueFrontend.queryBits kind w t s).length+answer.length+(b+1+2)+2)+2≤1000*((CliqueFrontend.time kind).eval N+N+answer.length+2)
  omega
noncomputable def time : Polynomial ℕ := 1000*(CliqueFrontend.time kind+X+2)

theorem program_polynomial (g : BitString → ℕ) (w : PairInput) (t s : ℕ) :
    ∃c, (program kind).Executes g (store (pairInputBits w) t s [])
      (store (pairInputBits w) t s (signedBits (g (CliqueFrontend.queryBits kind w t s):ℤ))) c ∧
      c ≤ (time kind).eval ((pairInputBits w).length+t+s+(signedBits (g (CliqueFrontend.queryBits kind w t s):ℤ)).length) := by
  obtain ⟨c,hc,hb⟩ := program_executes kind g w t s
  refine ⟨c,hc,hb.trans ?_⟩
  let N := (pairInputBits w).length+t+s
  let z := g (CliqueFrontend.queryBits kind w t s)
  have hm := polynomial_nat_eval_mono (CliqueFrontend.time kind) (show N ≤ N+(signedBits (z:ℤ)).length by omega)
  dsimp only at hm
  have hz : (Computability.encodeNat z).length ≤ (signedBits (z:ℤ)).length := by simp only [signedBits,List.length_cons,Int.natAbs_natCast];omega
  change 1000*((CliqueFrontend.time kind).eval N+N+(Computability.encodeNat z).length+2) ≤ _
  simp only [time,eval_mul,eval_add,eval_X,eval_ofNat]
  change _ ≤ 1000*((CliqueFrontend.time kind).eval (N+(signedBits (z:ℤ)).length)+(N+(signedBits (z:ℤ)).length)+2)
  omega
end HiddenCircuits.GraphReduction.Runtime.PairEval.CliqueAnswer
