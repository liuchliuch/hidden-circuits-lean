import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! Fixed finite branch trees whose leaves are actual finite programs. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock
variable {k : ℕ}

noncomputable def bitProgramChoice : List (Fin (k+1)) → (List Bool → OracleBlock k) → OracleBlock k
  | [],f => f []
  | i::is,f => branchPop i skip
      (bitProgramChoice is (fun bs => f (false::bs))) (bitProgramChoice is (fun bs => f (true::bs)))

theorem bitProgramChoice_executes (is : List (Fin (k+1))) (hn : is.Nodup)
    (f : List Bool → OracleBlock k) (bits : Fin (k+1) → Bool) (g : BitString → ℕ)
    (s t : Store k) (hs : ∀ i∈is, s i=[bits i]) (c : ℕ)
    (h : (f (is.map bits)).Executes g (eraseStore is s) t c) :
    (bitProgramChoice is f).Executes g s t (2*is.length+c) := by
  induction is generalizing s f with
  | nil => simpa [bitProgramChoice,eraseStore] using h
  | cons i is ih =>
    have hni := (List.nodup_cons.mp hn).1
    have hnt := (List.nodup_cons.mp hn).2
    have htail : ∀ j∈is, Function.update s i [] j=[bits j] := by
      intro j hj
      rw [Function.update_of_ne (by intro he;subst j;exact hni hj)]
      exact hs j (by simp [hj])
    have he := eraseStore_cons i is s
    have hi := ih hnt (s:=Function.update s i []) (f:=fun bs => f (bits i::bs)) htail (by simpa [he] using h)
    have hsi := hs i (by simp)
    cases hb : bits i
    · have hh := branchPop_false i skip
        (bitProgramChoice is (fun bs => f (false::bs))) (bitProgramChoice is (fun bs => f (true::bs))) g
        (rest:=[]) (by simpa [hb] using hsi) (by simpa [hb] using hi)
      simpa only [bitProgramChoice,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
    · have hh := branchPop_true i skip
        (bitProgramChoice is (fun bs => f (false::bs))) (bitProgramChoice is (fun bs => f (true::bs))) g
        (rest:=[]) (by simpa [hb] using hsi) (by simpa [hb] using hi)
      simpa only [bitProgramChoice,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

lemma bitProgramChoice_queryFree (is : List (Fin (k+1))) (f : List Bool → OracleBlock k)
    (hf : ∀ bs, (f bs).QueryFree) : (bitProgramChoice is f).QueryFree := by
  induction is generalizing f with
  | nil => exact hf []
  | cons i is ih => exact branchPop_queryFree _ _ _ _ skip_queryFree (ih _ (fun bs => hf _)) (ih _ (fun bs => hf _))

end HiddenCircuits.GraphReduction.Runtime
