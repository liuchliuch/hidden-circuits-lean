import HiddenCircuits.Complexity.GraphVerifier.MatchingRowsCorrectness
import HiddenCircuits.Complexity.GraphVerifier.MatchingGuardRuntime
import HiddenCircuits.Complexity.GraphVerifier.MatchingAllPairsFrame
import HiddenCircuits.Complexity.GraphVerifier.MatchingRowsFrame

/-! A complete ordinary-input perfect-matching verifier with actual polynomial machine runtime. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open OracleBlock Polynomial

def guardEmbedding : Fin 38 ↪ Fin 48 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 48 => z.val) h)

def finalScanEmbedding : Fin 18 ↪ Fin 48 where
  toFun i := ⟨if i.val=0 then 8 else if i.val=1 then 26 else if i.val=2 then 27
    else if i.val=3 then 4 else if i.val=4 then 0 else i.val+23,by split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun z : Fin 48 => z.val) h
    change (if i.val=0 then 8 else if i.val=1 then 26 else if i.val=2 then 27
      else if i.val=3 then 4 else if i.val=4 then 0 else i.val+23)=
      (if j.val=0 then 8 else if j.val=1 then 26 else if j.val=2 then 27
      else if j.val=3 then 4 else if j.val=4 then 0 else j.val+23) at hh
    split_ifs at hh <;> omega

def finalRowsEmbedding : Fin 6 ↪ Fin 48 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 41 else if i.val=2 then 0
    else if i.val=3 then 28 else if i.val=4 then 42 else 43
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def trueBranch : OracleBlock 47 :=
  seq (push 28 true) (seq (allPairsOn finalScanEmbedding)
    (seq (oneRowsOn finalRowsEmbedding) (seq (clear 0) (reverseOn 28 0 (by decide)))))
noncomputable def verifierBlock : OracleBlock 47 :=
  seq (rename guardBlock guardEmbedding) (branchPop 25 (Runtime.writeBool 0 false) (Runtime.writeBool 0 false) trueBranch)

def wideGuarded (xs a b : BitString) : Store 47 := fun i =>
  if h:i.val<38 then guardedStore xs a b ⟨i.val,h⟩ else []
def afterGuard (xs a b : BitString) : Store 47 := Function.update (wideGuarded xs a b) 25 []

theorem wideGuard_executes (g : BitString → ℕ) (xs : BitString) :
    ∃ a b cost, (rename guardBlock guardEmbedding).Executes g
      (Function.update (fun _ : Fin 48 => ([]:BitString)) 0 xs) (wideGuarded xs a b) cost ∧
      cost≤52*xs.length^2+92*xs.length+158 := by
  obtain ⟨a,b,c,hc,hcb⟩ := guard_executes g xs
  refine ⟨a,b,c,?_,hcb⟩
  apply rename_executes_to guardBlock guardEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;simp [guardEmbedding,wideGuarded,i.isLt]
  · intro j hj
    have hi : ¬j.val<38 := by intro h;exact hj ⟨j.val,h⟩ (Fin.ext rfl)
    have hj0 : j≠0 := by intro h;subst j;exact hi (by decide)
    simp [wideGuarded,hi,hj0]

theorem trueBranch_executes (g : BitString → ℕ) (xs a b : BitString) (hg : guardValue xs=true) :
    ∃ s cost, trueBranch.Executes g (afterGuard xs a b) s cost ∧
      s 0=[scanPairs (parse (parse xs).left).left.length (parse (parse xs).left).right (parse xs).right &&
        decide (RowsOne (parse (parse xs).left).left.length (parse xs).right)] ∧
      cost≤56*xs.length^4+118*xs.length^3+152*xs.length^2+33*xs.length+23 := by
  let n := (parse (parse xs).left).left.length
  let p := (parse (parse xs).left).right
  let w := (parse xs).right
  let v := scanPairs n p w
  let z := allRowsValue n w 0 n v
  let s₀ := afterGuard xs a b
  let s₁ := Function.update s₀ (28:Fin 48) [true]
  have h₁ : (push (28:Fin 48) true).Executes g s₀ s₁ 1 := push_executes g _ true s₀
  have hlen := guard_implies_lengths xs hg
  obtain ⟨c,hc,hcb⟩ := allPairsOn_executes finalScanEmbedding g s₁ n p w true hlen.1 hlen.2
    (by funext i;fin_cases i <;> rfl)
  let s₂ := Function.update (Function.update s₁ (26:Fin 48) (List.replicate n true)) (28:Fin 48) [v]
  have h₂ : (allPairsOn finalScanEmbedding).Executes g s₁ s₂ c := hc
  let s₃ := Function.update (Function.update s₂ (0:Fin 48) (w.drop (n*n))) (28:Fin 48) [z]
  have h₃ : (oneRowsOn finalRowsEmbedding).Executes g s₂ s₃ (7*n*n+14*n+5) :=
    oneRowsOn_executes finalRowsEmbedding g s₂ n w v hlen.2 (by funext i;fin_cases i <;> rfl)
  let s₄ := Function.update s₃ (0:Fin 48) []
  have h₄ : (clear (0:Fin 48)).Executes g s₃ s₄ ((w.drop (n*n)).length+1) := clear_executes g _ s₃
  let s₅ := Function.update (Function.update s₄ (28:Fin 48) []) (0:Fin 48) [z]
  have h₅ : (reverseOn (28:Fin 48) 0 (by decide)).Executes g s₄ s₅ 3 := reverseOn_executes g _ _ _ s₄
  refine ⟨s₅,1+(c+((7*n*n+14*n+5)+(((w.drop (n*n)).length+1)+3+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅))),?_,?_⟩
  · change [z]=[_]
    exact congrArg (fun b => [b]) (allRowsValue_iff n w v hlen.2)
  · have hb := Runtime.guard_data_bounds xs
    have hm : 56*n^4+118*n^3+145*n^2+18*n+5≤
        56*xs.length^4+118*xs.length^3+145*xs.length^2+18*xs.length+5 := by
      have hn : n≤xs.length := hb.1
      gcongr
    have hn : n≤xs.length := hb.1
    have hn2 := Nat.mul_le_mul hn hn
    have hw : w.length≤xs.length := hb.2.2
    have hd : w.length-n*n≤w.length := Nat.sub_le _ _
    simp only [List.length_drop]
    nlinarith

theorem trueBranch_queryFree : trueBranch.QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (allPairsOn_queryFree _)
    (seq_queryFree _ _ (oneRowsOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _))))

theorem verifierBlock_queryFree : verifierBlock.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ guard_queryFree)
    (branchPop_queryFree _ _ _ _ (Runtime.writeBool_queryFree _ _) (Runtime.writeBool_queryFree _ _) trueBranch_queryFree)

theorem verifierBlock_executes (xs : BitString) :
    ∃ s : Store 47, ∃ cost, verifierBlock.Executes (fun _ => 0)
      (Function.update (fun _ : Fin 48 => ([]:BitString)) 0 xs) s cost ∧
      s 0=Computability.encodeBool (Matching.verifier xs) ∧ cost≤2000*(xs.length+1)^4 := by
  obtain ⟨a,b,c,hc,hcb⟩ := wideGuard_executes (fun _ => 0) xs
  cases hg : guardValue xs with
  | false =>
    let s := Function.update (afterGuard xs a b) (0:Fin 48) [false]
    have hb := Runtime.writeBool_executes (0:Fin 48) false (fun _ => 0) (afterGuard xs a b)
    have hbranch := branchPop_false (25:Fin 48) (Runtime.writeBool 0 false) (Runtime.writeBool 0 false) trueBranch (fun _ => 0)
      (s := wideGuarded xs a b) (rest := [])
      (show wideGuarded xs a b 25=false::[] by change [guardValue xs]=[false];rw [hg]) hb
    have hout : s 0=Computability.encodeBool (Matching.verifier xs) := by
      change [false]=Computability.encodeBool (Matching.verifier xs)
      rw [verifier_eq_guard_scan,hg]
      rfl
    refine ⟨s,c+(((afterGuard xs a b) 0).length+4+2)+2,seq_executes _ _ (fun _ => 0) hc hbranch,hout,?_⟩
    have hw : ((afterGuard xs a b) 0).length≤xs.length := (Runtime.parse_lengths xs).2
    nlinarith
  | true =>
    obtain ⟨s,d,hd,hout,hdb⟩ := trueBranch_executes (fun _ => 0) xs a b hg
    have hbranch := branchPop_true (25:Fin 48) (Runtime.writeBool 0 false) (Runtime.writeBool 0 false) trueBranch (fun _ => 0)
      (s := wideGuarded xs a b) (rest := [])
      (show wideGuarded xs a b 25=true::[] by change [guardValue xs]=[true];rw [hg]) hd
    refine ⟨s,c+(d+2)+2,seq_executes _ _ (fun _ => 0) hc hbranch,?_,?_⟩
    · rw [hout,verifier_eq_guard_scan,hg]
      rfl
    · nlinarith

theorem perfectMatching_polyVerifier : PolyVerifier Matching.verifier := by
  apply polyVerifier_of_block Matching.verifier verifierBlock verifierBlock_queryFree (2000*(X+1)^4)
  intro xs
  obtain ⟨s,c,hc,ho,hb⟩ := verifierBlock_executes xs
  refine ⟨s,c,hc,ho,?_⟩
  simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one] using hb

theorem perfectMatching_sharpP : SharpP GraphInput.perfectMatchingProblem := by
  refine ⟨X*X,Matching.verifier,perfectMatching_polyVerifier,?_⟩
  intro xs
  simpa using (Matching.certificateCount_eq xs).symm
end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
