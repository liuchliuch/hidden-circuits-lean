import HiddenCircuits.Approximation.SelfReduction.HeavyBranch

/-! Right-biased maximum fold
semantics, including exact agreement with the recursive finite argmax. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime

def keepBetter (a b : ℕ × ℕ) : ℕ × ℕ := if a.1 ≤ b.1 then b else a

theorem keepBetter_assoc (a b c : ℕ × ℕ) :
    keepBetter (keepBetter a b) c = keepBetter a (keepBetter b c) := by
  unfold keepBetter
  split_ifs <;> simp_all <;> omega

def indexedCounts : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | x::xs, pos => (x,pos)::indexedCounts xs (pos+1)

def scanCounts (xs : List ℕ) (best idx pos : ℕ) : ℕ × ℕ :=
  (indexedCounts xs pos).foldl keepBetter (best,idx)

@[simp] theorem scanCounts_nil (best idx pos : ℕ) : scanCounts [] best idx pos=(best,idx) := rfl

 theorem scanCounts_cons (x : ℕ) (xs : List ℕ) (best idx pos : ℕ) :
    scanCounts (x::xs) best idx pos =
      scanCounts xs (keepBetter (best,idx) (x,pos)).1 (keepBetter (best,idx) (x,pos)).2 (pos+1) := by
  simp [scanCounts,indexedCounts]

private theorem scan_shift (n : ℕ) (q : Fin (n+1) → ℕ) (pos : ℕ) (a : ℕ × ℕ) :
    (List.ofFn (fun i => (q i,pos+i.val))).foldl keepBetter a =
      keepBetter a (q (chooseMax n q),pos+(chooseMax n q).val) := by
  induction n generalizing pos a with
  | zero => simp [List.ofFn_succ,chooseMax]
  | succ n ih =>
    rw [List.ofFn_succ,List.foldl_cons]
    have hvec : (fun i : Fin (n+1) => (q i.succ,pos+i.succ.val)) =
        (fun i : Fin (n+1) => (q i.succ,(pos+1)+i.val)) := by
      funext i; simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    rw [hvec,ih,keepBetter_assoc]
    simp only [Fin.val_zero,Nat.add_zero,chooseMax]
    split_ifs with h
    · simp only [keepBetter,if_pos h,Fin.val_succ]
      congr 2 <;> omega
    · simp only [keepBetter,if_neg h,Fin.val_zero,Nat.add_zero]

 theorem scan_ofFn_eq_chooseMax (n : ℕ) (q : Fin (n+1) → ℕ) :
    (List.ofFn (fun i => (q i,i.val))).foldl keepBetter (0,0) =
      (q (chooseMax n q),(chooseMax n q).val) := by
  simpa [keepBetter] using scan_shift n q 0 (0,0)

end HiddenCircuits.Approximation.SelfReduction.Runtime
