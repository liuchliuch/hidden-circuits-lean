import HiddenCircuits.ExactSampling.Runtime.FairDraw

/-! Exhaustive rejection traces realized by the finite fair-coin driver, with
full physical cost (including all copies, retries, and normalization). -/
namespace HiddenCircuits.ExactSampling.Runtime.FairDraw
open Complexity OracleBlock BinaryArithmetic Approximation Approximation.FiniteChains Rejection
open scoped BigOperators

 def fairReads {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) : BitString :=
  (List.ofFn (fun j => (List.ofFn (r j).val).reverse)).flatten ++
    (List.ofFn (acceptedTape hn i)).reverse

 theorem fairReads_length {n : ℕ} (hn : 0<n) (t : ℕ) (r : Trace n t) (i : Fin n) :
    (fairReads hn t r i).length=(t+1)*width n := by
  simp [fairReads,List.length_flatten,List.sum_ofFn]
  ring

 theorem loop_runs {n : ℕ} (hn : 0<n) (graph : BitString) (t : ℕ) (r : Trace n t) (i : Fin n) :
    ∃c,FairCode.Runs loop (ready graph n [] [true] []) (result graph i.val)
      (fairReads hn t r i) c ∧c≤(t+1)*120*(Nat.size n+1) := by
  have hp : Function.update (ready graph n [] [true] []) (3:Fin 66) []=ready graph n [] [] [] := by
    funext j;fin_cases j <;> simp [ready,state]
  induction t with
  | zero =>
    obtain ⟨c,hc,hb⟩ := body_accept hn graph i
    have ht : FairCode.Runs loop (result graph i.val) (result graph i.val) [] 1 :=
      FairCode.Runs.loopEmpty _ rfl
    have hh := FairCode.Runs.loopTrue (q:=(3:Fin 66)) (B:=body) (C:=body)
      (s:=ready graph n [] [true] []) (rest:=[]) rfl (by rw [hp];exact hc) ht
    refine ⟨1+c+1+1,?_,?_⟩
    · simpa [fairReads] using hh
    · nlinarith
  | succ t ih =>
    obtain ⟨c,hc,hb⟩ := body_reject graph n (r 0)
    obtain ⟨d,hd,hdb⟩ := ih (fun j => r j.succ)
    have hh := FairCode.Runs.loopTrue (q:=(3:Fin 66)) (B:=body) (C:=body)
      (s:=ready graph n [] [true] []) (rest:=[]) rfl (by rw [hp];exact hc) hd
    refine ⟨1+c+1+d,?_,?_⟩
    · simpa [fairReads,List.ofFn_succ,List.append_assoc] using hh
    · nlinarith

 theorem loop_queryFree : loop.QueryFree := by
  have ht : trial.QueryFree := rename_queryFree _ _ RejectionTrial.queryFree
  have hr : reject.QueryFree := seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)
  have ha : accept.QueryFree := seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (rename_queryFree _ _ subBlock_queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))
  have hd : draw.QueryFree := ⟨copyOn_queryFree _ _ _ _ _ _,FairFill.queryFree _ _⟩
  exact ⟨⟨hd,ht,hr,hr,ha⟩,⟨hd,ht,hr,hr,ha⟩⟩

/-- The full charged rejection driver has linear expected bit work in the
binary size of the count, including all rejected trials. -/
 theorem expected_work_le {n : ℕ} (hn : 0<n) :
    ∑'t, ((t+1 : ℕ) : ℝ)*120*(Nat.size n+1)*(n : ℝ)*outcomeMass n t≤
      240*(Nat.size n+1) := by
  have hh := (weighted_attempts_hasSum hn).mul_left (120*((Nat.size n : ℝ)+1))
  have he : (∑'t, ((t+1 : ℕ) : ℝ)*120*(Nat.size n+1)*(n : ℝ)*outcomeMass n t)=
      (120*((Nat.size n : ℝ)+1))*expectedAttempts n := by
    convert hh.tsum_eq using 1
    congr 1
    funext t
    ring
  rw [he]
  nlinarith [expectedAttempts_lt_two hn]

end HiddenCircuits.ExactSampling.Runtime.FairDraw
