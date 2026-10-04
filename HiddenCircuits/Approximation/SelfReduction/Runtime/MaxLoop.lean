import HiddenCircuits.Approximation.SelfReduction.Runtime.MaxBody

/-! Execution and bounds for the physical maximum scan. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def maximumScan : OracleBlock 10 := whilePop 3 skip maxBody

 theorem maximumScan_execution (g : BitString → ℕ) (xs : List ℕ) (best idx pos B : ℕ)
    (hbest : best ≤ B) (hidx : idx ≤ pos) (hxs : ∀ x ∈ xs, x ≤ B) :
    ∃ t, WhileExecution (3 : Fin 11) skip maxBody g
      (maxStore best idx pos 0 (encodeBitList (xs.map (fun x => List.replicate x true))) [])
      (maxStore (scanCounts xs best idx pos).1 (scanCounts xs best idx pos).2 (pos+xs.length) 0 [] []) t ∧
      t ≤ 1+xs.length*(50*(B+pos+xs.length+1)) := by
  induction xs generalizing best idx pos with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [encodeBitList] using (WhileExecution.empty (maxStore best idx pos 0 [] []) (by rfl))
  | cons x xs ih =>
    let pair := keepBetter (best,idx) (x,pos)
    have hx := hxs x (List.mem_cons_self)
    have hpb : pair.1 ≤ B := by dsimp [pair,keepBetter]; split_ifs <;> assumption
    have hpi : pair.2 ≤ pos+1 := by dsimp [pair,keepBetter]; split_ifs <;> omega
    obtain ⟨tb,hb,hbt⟩ := maxBody_executes g best idx pos x
      (encodeBitList (xs.map (fun x => List.replicate x true)))
    obtain ⟨tt,ht,htt⟩ := ih pair.1 pair.2 (pos+1) hpb hpi
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have hpop : Function.update
        (maxStore best idx pos 0 (encodeBitList ((x::xs).map (fun x => List.replicate x true))) [])
        (3 : Fin 11) (pairBits (List.replicate x true) (encodeBitList (xs.map (fun x => List.replicate x true)))) =
        maxStore best idx pos 0 (pairBits (List.replicate x true) (encodeBitList (xs.map (fun x => List.replicate x true)))) [] := by
      funext i; fin_cases i <;> rfl
    have hw := WhileExecution.one
      (s := maxStore best idx pos 0 (encodeBitList ((x::xs).map (fun x => List.replicate x true))) [])
      (rest := pairBits (List.replicate x true) (encodeBitList (xs.map (fun x => List.replicate x true))))
      (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨2+tb+tt,?_,?_⟩
    · convert hw using 1
      · simp only [scanCounts_cons,List.length_cons,Nat.add_assoc]
        congr 1 <;> omega
      · omega
    · have hbody : tb+2 ≤ 50*(B+pos+xs.length+2) := by omega
      simp only [List.length_cons]
      have hh : B+(pos+1)+xs.length+1=B+pos+xs.length+2 := by omega
      rw [hh] at htt
      nlinarith
 theorem maximumScan_executes (g : BitString → ℕ) (xs : List ℕ) (best idx pos B : ℕ)
    (hbest : best≤B) (hidx : idx≤pos) (hxs : ∀ x ∈ xs, x≤B) :
    ∃ t, maximumScan.Executes g
      (maxStore best idx pos 0 (encodeBitList (xs.map (fun x => List.replicate x true))) [])
      (maxStore (scanCounts xs best idx pos).1 (scanCounts xs best idx pos).2 (pos+xs.length) 0 [] []) t ∧
      t ≤ 1+xs.length*(50*(B+pos+xs.length+1)) := by
  obtain ⟨t,ht,hb⟩ := maximumScan_execution g xs best idx pos B hbest hidx hxs
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩

 theorem indexedCounts_ofFn (n : ℕ) (q : Fin n → ℕ) (pos : ℕ) :
    indexedCounts (List.ofFn q) pos = List.ofFn (fun i => (q i,pos+i.val)) := by
  induction n generalizing pos with
  | zero => simp [indexedCounts]
  | succ n ih =>
    rw [List.ofFn_succ, indexedCounts, List.ofFn_succ, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    congr 1
    omega

/-- The actual finite machine returns exactly the same index as `chooseMax`.
Its time is polynomial in vector length and the bounded unary values. -/
theorem maximumScan_chooseMax (g : BitString → ℕ) (n B : ℕ) (q : Fin (n+1) → ℕ)
    (hq : ∀ i, q i≤B) :
    ∃ t, maximumScan.Executes g
      (maxStore 0 0 0 0 (encodeBitList ((List.ofFn q).map (fun x => List.replicate x true))) [])
      (maxStore (q (chooseMax n q)) (chooseMax n q).val (n+1) 0 [] []) t ∧
      t ≤ 1+(n+1)*(50*(B+n+2)) := by
  obtain ⟨t,ht,hb⟩ := maximumScan_executes g (List.ofFn q) 0 0 0 B (by omega) (by omega)
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hq i)
  have he : scanCounts (List.ofFn q) 0 0 0 = (q (chooseMax n q),(chooseMax n q).val) := by
    unfold scanCounts
    rw [indexedCounts_ofFn]
    simpa using scan_ofFn_eq_chooseMax n q
  refine ⟨t,?_,?_⟩
  · rw [he] at ht
    simpa only [List.length_ofFn, zero_add] using ht
  · simpa [Nat.add_assoc] using hb

end HiddenCircuits.Approximation.SelfReduction.Runtime
