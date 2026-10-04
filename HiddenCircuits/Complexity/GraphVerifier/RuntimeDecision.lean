import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! Fixed finite Boolean decision trees compiled to actual pop/push blocks. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock
variable {k : ℕ}

noncomputable def writeBool (out : Fin (k+1)) (b : Bool) : OracleBlock k :=
  seq (clear out) (push out b)

 theorem writeBool_executes (out : Fin (k+1)) (b : Bool) (g : BitString → ℕ) (s : Store k) :
    (writeBool out b).Executes g s (Function.update s out [b]) ((s out).length+4) := by
  have h := seq_executes (clear out) (push out b) g (clear_executes g out s)
    (push_executes g out b (Function.update s out []))
  simpa only [writeBool,Function.update_self,Function.update_idem,Nat.add_assoc] using h

 theorem writeBool_queryFree (out : Fin (k+1)) (b : Bool) : (writeBool out b).QueryFree :=
  seq_queryFree _ _ (clear_queryFree out) (push_queryFree out b)

/-- No Boolean function is a runtime primitive: its constant truth table is compiled into the leaves. -/
noncomputable def decision (out : Fin (k+1)) : List (Fin (k+1)) → (List Bool → Bool) → OracleBlock k
  | [],f => writeBool out (f [])
  | i::is,f => branchPop i (writeBool out false)
      (decision out is (fun bs => f (false::bs))) (decision out is (fun bs => f (true::bs)))

 theorem decision_queryFree (out : Fin (k+1)) (is : List (Fin (k+1))) (f : List Bool → Bool) :
    (decision out is f).QueryFree := by
  induction is generalizing f with
  | nil => exact writeBool_queryFree out _
  | cons i is ih => exact branchPop_queryFree _ _ _ _ (writeBool_queryFree out false) (ih _) (ih _)

/-- On the declared singleton inputs, the decision tree consumes each input once,
leaves every other register untouched, and charges each real branch and final write. -/
theorem decision_executes (out : Fin (k+1)) (is : List (Fin (k+1))) (hn : is.Nodup)
    (hout : out∉is) (f : List Bool → Bool) (bits : Fin (k+1) → Bool)
    (g : BitString → ℕ) (s : Store k) (hs : ∀ i∈is, s i=[bits i]) :
    (decision out is f).Executes g s
      (Function.update (eraseStore is s) out [f (is.map bits)])
      (2*is.length+(s out).length+4) := by
  induction is generalizing s f with
  | nil => simpa [decision,eraseStore] using writeBool_executes out (f []) g s
  | cons i is ih =>
    have hni : i∉is := (List.nodup_cons.mp hn).1
    have hnt := (List.nodup_cons.mp hn).2
    have hno : out≠i ∧ out∉is := by simpa using hout
    have hoi := hno.1
    have hot := hno.2
    have htail : ∀ j∈is, Function.update s i [] j=[bits j] := by
      intro j hj
      rw [Function.update_of_ne (by intro he; subst j; exact hni hj)]
      exact hs j (by simp [hj])
    have hsi := hs i (by simp)
    have hi := ih hnt hot (s := Function.update s i [])
      (f := fun bs => f (bits i::bs)) htail
    have he : eraseStore (i::is) s=eraseStore is (Function.update s i []) := eraseStore_cons i is s
    have ho : Function.update s i [] out=s out := Function.update_of_ne hoi _ _
    cases hb : bits i with
    | false =>
      have hstep := branchPop_false i (writeBool out false)
        (decision out is (fun bs => f (false::bs))) (decision out is (fun bs => f (true::bs))) g
        (rest := []) (by simpa [hb] using hsi) (by simpa [hb] using hi)
      simpa only [decision,he,List.map_cons,hb,List.length_cons,ho,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hstep
    | true =>
      have hstep := branchPop_true i (writeBool out false)
        (decision out is (fun bs => f (false::bs))) (decision out is (fun bs => f (true::bs))) g
        (rest := []) (by simpa [hb] using hsi) (by simpa [hb] using hi)
      simpa only [decision,he,List.map_cons,hb,List.length_cons,ho,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hstep

end HiddenCircuits.Complexity.GraphVerifier.Runtime
