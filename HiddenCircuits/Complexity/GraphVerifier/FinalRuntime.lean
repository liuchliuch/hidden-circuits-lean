import HiddenCircuits.Complexity.GraphVerifier.GuardRuntime
import HiddenCircuits.Complexity.GraphVerifier.AllPairsFrame

/-! One actual finite polynomial-time verifier, with malformed-input rejection and canonical output. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock
open Polynomial

def finalScanEmbedding : Fin 18 ↪ Fin 38 where
  toFun i := ⟨if i.val=0 then 8 else if i.val=1 then 23 else if i.val=2 then 24
    else if i.val=3 then 4 else if i.val=4 then 0 else i.val+20,by split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun z : Fin 38 => z.val) h
    change (if i.val=0 then 8 else if i.val=1 then 23 else if i.val=2 then 24
      else if i.val=3 then 4 else if i.val=4 then 0 else i.val+20)=
      (if j.val=0 then 8 else if j.val=1 then 23 else if j.val=2 then 24
      else if j.val=3 then 4 else if j.val=4 then 0 else j.val+20) at hh
    split_ifs at hh <;> omega

noncomputable def trueBranch : OracleBlock 37 :=
  seq (push 25 true) (seq (allPairsOn finalScanEmbedding) (seq (clear 0) (reverseOn 25 0 (by decide))))
noncomputable def verifierBlock : OracleBlock 37 :=
  seq guardBlock (branchPop 18 (writeBool 0 false) (writeBool 0 false) trueBranch)

def afterGuard (xs a b : BitString) : Store 37 := Function.update (guardedStore xs a b) 18 []

 theorem trueBranch_executes (g : BitString → ℕ) (xs a b : BitString) (hg : guardValue xs=true) :
    ∃ s cost, trueBranch.Executes g (afterGuard xs a b) s cost ∧
      s 0=[scanPairs (parse (parse xs).left).left.length (parse (parse xs).left).right (parse xs).right] ∧
      cost≤28*xs.length^4+88*xs.length^3+117*xs.length^2+19*xs.length+16 := by
  let n := (parse (parse xs).left).left.length
  let p := (parse (parse xs).left).right
  let w := (parse xs).right
  let v := scanPairs n p w
  let s₀ := afterGuard xs a b
  let s₁ := Function.update s₀ (25:Fin 38) [true]
  have h₁ : (push (25:Fin 38) true).Executes g s₀ s₁ 1 := push_executes g _ true s₀
  have hlen := guard_implies_lengths xs hg
  obtain ⟨c,hc,hcb⟩ := allPairsOn_executes finalScanEmbedding g s₁ n p w true hlen.1 hlen.2
    (by funext i;fin_cases i <;> rfl)
  let s₂ := Function.update (Function.update s₁ (23:Fin 38) (List.replicate n true)) (25:Fin 38) [v]
  have h₂ : (allPairsOn finalScanEmbedding).Executes g s₁ s₂ c := hc
  let s₃ := Function.update s₂ (0:Fin 38) []
  have h₃ : (clear (0:Fin 38)).Executes g s₂ s₃ (w.length+1) := clear_executes g _ s₂
  let s₄ := Function.update (Function.update s₃ (25:Fin 38) []) (0:Fin 38) [v]
  have h₄ : (reverseOn (25:Fin 38) 0 (by decide)).Executes g s₃ s₄ 3 := reverseOn_executes g _ _ _ s₃
  refine ⟨s₄,1+(c+((w.length+1)+3+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),rfl,?_⟩
  have hb := guard_data_bounds xs
  have hm : 28*n^4+88*n^3+117*n^2+18*n+5≤
      28*xs.length^4+88*xs.length^3+117*xs.length^2+18*xs.length+5 := by
    have hn : n≤xs.length := hb.1
    gcongr
  have hw : w.length≤xs.length := hb.2.2
  omega

 theorem trueBranch_queryFree : trueBranch.QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (allPairsOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))

 theorem verifierBlock_queryFree : verifierBlock.QueryFree :=
  seq_queryFree _ _ guard_queryFree (branchPop_queryFree _ _ _ _ (writeBool_queryFree _ _)
    (writeBool_queryFree _ _) trueBranch_queryFree)

/-- Every raw binary string reaches a canonical one-bit Boolean output with a polynomial real step count. -/
theorem verifierBlock_executes (xs : BitString) :
    ∃ s : Store 37, ∃ cost, verifierBlock.Executes (fun _ => 0)
      (Function.update (fun _ : Fin 38 => ([]:BitString)) 0 xs) s cost ∧
      s 0=Computability.encodeBool (verifier xs) ∧ cost≤1000*(xs.length+1)^4 := by
  obtain ⟨a,b,c,hc,hcb⟩ := guard_executes (fun _ => 0) xs
  cases hg : guardValue xs with
  | false =>
    let s := Function.update (afterGuard xs a b) (0:Fin 38) [false]
    have hb := writeBool_executes (0:Fin 38) false (fun _ => 0) (afterGuard xs a b)
    have hbranch := branchPop_false (18:Fin 38) (writeBool 0 false) (writeBool 0 false) trueBranch (fun _ => 0)
      (s := guardedStore xs a b) (rest := [])
      (show guardedStore xs a b 18=false::[] by change [guardValue xs]=[false];rw [hg]) hb
    have hout : s 0=Computability.encodeBool (verifier xs) := by
      change [false]=Computability.encodeBool (verifier xs)
      rw [verifier_eq_guard_scan,hg]
      rfl
    refine ⟨s,c+(((afterGuard xs a b) 0).length+4+2)+2,seq_executes _ _ (fun _ => 0) hc hbranch,hout,?_⟩
    have hw : ((afterGuard xs a b) 0).length≤xs.length := (parse_lengths xs).2
    nlinarith
  | true =>
    obtain ⟨s,d,hd,hout,hdb⟩ := trueBranch_executes (fun _ => 0) xs a b hg
    have hbranch := branchPop_true (18:Fin 38) (writeBool 0 false) (writeBool 0 false) trueBranch (fun _ => 0)
      (s := guardedStore xs a b) (rest := [])
      (show guardedStore xs a b 18=true::[] by change [guardValue xs]=[true];rw [hg]) hd
    refine ⟨s,c+(d+2)+2,seq_executes _ _ (fun _ => 0) hc hbranch,?_,?_⟩
    · rw [hout,verifier_eq_guard_scan,hg]
      rfl
    · nlinarith

/-- Genuine mathlib-TM2 polynomial verifier; cleanup is itself a checked instruction program. -/
theorem independentSet_polyVerifier : PolyVerifier verifier := by
  apply polyVerifier_of_block verifier verifierBlock verifierBlock_queryFree (1000*(X+1)^4)
  intro xs
  obtain ⟨s,c,hc,ho,hb⟩ := verifierBlock_executes xs
  refine ⟨s,c,hc,ho,?_⟩
  simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one] using hb

/-- The ordinary malformed-input-aware independent-set counting problem belongs to #P. -/
theorem independentSet_sharpP : SharpP GraphInput.independentSetProblem := by
  refine ⟨X,verifier,independentSet_polyVerifier,?_⟩
  intro xs
  simpa using (certificateCount_eq xs).symm

end HiddenCircuits.Complexity.GraphVerifier.Runtime
