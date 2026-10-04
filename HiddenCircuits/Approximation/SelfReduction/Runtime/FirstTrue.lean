import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! Actual least-retained-vertex search on a bit mask, preserving the mask. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def seekPos : BitString → ℕ
  | [] => 0
  | false::xs => seekPos xs+1
  | true::_ => 0

def seekFound : BitString → Bool
  | [] => false
  | false::xs => seekFound xs
  | true::_ => true

def seekRest : BitString → BitString
  | [] => []
  | false::xs => seekRest xs
  | true::xs => xs

 theorem seekPos_le_length (xs : BitString) : seekPos xs ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [seekPos] <;> omega

 theorem seekRest_length_le (xs : BitString) : (seekRest xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [seekRest] <;> omega

 theorem seekFound_eq_any (xs : BitString) : seekFound xs=xs.any id := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [seekFound,ih]

/-- This decomposition simultaneously proves that the returned position is
marked and every earlier position is false, or the entire mask is false. -/
theorem seek_decomposition (xs : BitString) :
    xs=List.replicate (seekPos xs) false ++ if seekFound xs then true::seekRest xs else [] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | true => rfl
    | false =>
      simp only [seekPos,seekFound,seekRest,List.replicate_succ]
      exact congrArg (List.cons false) ih

 theorem seekFound_true_spec (xs : BitString) (h : seekFound xs=true) :
    seekPos xs < xs.length ∧ xs[seekPos xs]?=some true ∧
      ∀ j < seekPos xs, xs[j]?=some false := by
  have hd := seek_decomposition xs
  have hlen := congrArg List.length hd
  simp [h] at hlen
  refine ⟨by omega,?_,?_⟩
  · calc
      xs[seekPos xs]? = (List.replicate (seekPos xs) false ++ if seekFound xs then true::seekRest xs else [])[seekPos xs]? :=
        congrArg (fun ys : BitString => ys[seekPos xs]?) hd
      _ = _ := by simp [h,List.getElem?_append]
  · intro j hj
    conv_lhs => rw [hd]
    simp [h,List.getElem?_append,hj]

 def retainedMask {n : ℕ} (U : Finset (Fin n)) : BitString := List.ofFn (fun v => decide (v ∈ U))

 theorem seekFound_retainedMask {n : ℕ} (U : Finset (Fin n)) (hU : U.Nonempty) :
    seekFound (retainedMask U)=true := by
  rw [seekFound_eq_any]
  obtain ⟨v,hv⟩ := hU
  apply List.any_eq_true.mpr
  refine ⟨true,?_,rfl⟩
  exact List.mem_ofFn.mpr ⟨v,by simp [hv]⟩

 theorem seekPos_retainedMask_min {n : ℕ} (U : Finset (Fin n)) (hU : U.Nonempty) :
    seekPos (retainedMask U)=(U.min' hU).val := by
  have hs := seekFound_true_spec (retainedMask U) (seekFound_retainedMask U hU)
  have hi : seekPos (retainedMask U) < n := by simpa [retainedMask] using hs.1
  let u : Fin n := ⟨seekPos (retainedMask U),hi⟩
  have hu : u ∈ U := by
    have hh := hs.2.1
    have hh' : ∃ h : seekPos (retainedMask U) < n, (⟨seekPos (retainedMask U),h⟩ : Fin n) ∈ U := by
      simpa [retainedMask,List.getElem?_ofFn] using hh
    obtain ⟨hb,hm⟩ := hh'
    exact hm
  have hlow : (U.min' hU).val ≤ u.val := Finset.min'_le U u hu
  have hupp : u.val ≤ (U.min' hU).val := by
    by_contra hh
    have hlt : (U.min' hU).val < seekPos (retainedMask U) := by dsimp [u] at hh; omega
    have hbad := hs.2.2 (U.min' hU).val hlt
    have hm := Finset.min'_mem U hU
    simpa [retainedMask,List.getElem?_ofFn,(U.min' hU).isLt,hm] using hbad
  exact Nat.le_antisymm hupp hlow

def searchStore (mask : BitString) (index : ℕ) (scan flag : BitString) : Store 4 := fun i =>
  if i.val=0 then mask else if i.val=1 then List.replicate index true
  else if i.val=2 then scan else if i.val=3 then flag else []

def firstTrueCore : OracleBlock 4 where
  labelCount := 5
  start := 0
  exit := 4
  code q := if q=0 then .pop 2 3 1 2
    else if q=1 then .push 1 true 0
    else if q=2 then .push 3 true 4
    else if q=3 then .push 3 false 4
    else .halt
  exit_halt := rfl

 theorem firstTrueCore_executes (g : BitString → ℕ) (mask scan flag : BitString) (index : ℕ) :
    firstTrueCore.Executes g (searchStore mask index scan flag)
      (searchStore mask (index+seekPos scan) (seekRest scan) (seekFound scan::flag)) (2*seekPos scan+2) := by
  induction scan generalizing index with
  | nil =>
    have h1 : firstTrueCore.machine.step g (firstTrueCore.config (0 : Fin 5) (searchStore mask index [] flag)) =
        some (firstTrueCore.config (3 : Fin 5) (searchStore mask index [] flag),1) := rfl
    have h2 : firstTrueCore.machine.step g (firstTrueCore.config (3 : Fin 5) (searchStore mask index [] flag)) =
        some (firstTrueCore.config (4 : Fin 5) (searchStore mask index [] (false::flag)),1) := by
      apply congrArg (fun c : firstTrueCore.machine.Config => some (c,1))
      apply OracleConfig.ext
      · rfl
      · intro i; fin_cases i <;> rfl
    simpa [seekPos,seekRest,seekFound] using (OracleMachine.Steps.single h1).trans (OracleMachine.Steps.single h2)
  | cons b scan ih =>
    cases b with
    | true =>
      have h1 : firstTrueCore.machine.step g (firstTrueCore.config (0 : Fin 5) (searchStore mask index (true::scan) flag)) =
          some (firstTrueCore.config (2 : Fin 5) (searchStore mask index scan flag),1) := by
        apply congrArg (fun c : firstTrueCore.machine.Config => some (c,1))
        apply OracleConfig.ext
        · rfl
        · intro i; fin_cases i <;> rfl
      have h2 : firstTrueCore.machine.step g (firstTrueCore.config (2 : Fin 5) (searchStore mask index scan flag)) =
          some (firstTrueCore.config (4 : Fin 5) (searchStore mask index scan (true::flag)),1) := by
        apply congrArg (fun c : firstTrueCore.machine.Config => some (c,1))
        apply OracleConfig.ext
        · rfl
        · intro i; fin_cases i <;> rfl
      simpa [seekPos,seekRest,seekFound] using (OracleMachine.Steps.single h1).trans (OracleMachine.Steps.single h2)
    | false =>
      have h1 : firstTrueCore.machine.step g (firstTrueCore.config (0 : Fin 5) (searchStore mask index (false::scan) flag)) =
          some (firstTrueCore.config (1 : Fin 5) (searchStore mask index scan flag),1) := by
        apply congrArg (fun c : firstTrueCore.machine.Config => some (c,1))
        apply OracleConfig.ext
        · rfl
        · intro i; fin_cases i <;> rfl
      have h2 : firstTrueCore.machine.step g (firstTrueCore.config (1 : Fin 5) (searchStore mask index scan flag)) =
          some (firstTrueCore.config (0 : Fin 5) (searchStore mask (index+1) scan flag),1) := by
        apply congrArg (fun c : firstTrueCore.machine.Config => some (c,1))
        apply OracleConfig.ext
        · rfl
        · intro i; fin_cases i <;> simp [OracleBlock.config,searchStore,List.replicate_succ]
      have h := (OracleMachine.Steps.single h1).trans ((OracleMachine.Steps.single h2).trans (ih (index+1)))
      convert h using 1
      · simp [seekPos,seekRest,seekFound,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> rfl
      · simp [seekPos]; omega

noncomputable def firstTrueMask : OracleBlock 4 :=
  seq (copyOn 0 2 4 (by decide) (by decide) (by decide)) (seq firstTrueCore (clear 2))

 theorem firstTrueMask_executes (g : BitString → ℕ) (mask : BitString) :
    ∃ t, firstTrueMask.Executes g (searchStore mask 0 [] [])
      (searchStore mask (seekPos mask) [] [seekFound mask]) t ∧ t ≤ 8*mask.length+9 := by
  have hc : (copyOn (0 : Fin 5) 2 4 (by decide) (by decide) (by decide)).Executes g
      (searchStore mask 0 [] []) (searchStore mask 0 mask []) (5*mask.length+2) := by
    convert copyOn_executes g (0 : Fin 5) 2 4 (by decide) (by decide) (by decide) (searchStore mask 0 [] []) rfl using 1
    funext i; fin_cases i <;> simp [searchStore]
  have hs := firstTrueCore_executes g mask mask [] 0
  simp only [zero_add] at hs
  have hclear : (clear (2 : Fin 5)).Executes g (searchStore mask (seekPos mask) (seekRest mask) [seekFound mask])
      (searchStore mask (seekPos mask) [] [seekFound mask]) ((seekRest mask).length+1) := by
    convert clear_executes g (2 : Fin 5) (searchStore mask (seekPos mask) (seekRest mask) [seekFound mask]) using 1
    funext i; fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hs hclear),?_⟩
  have hp := seekPos_le_length mask
  have hr := seekRest_length_le mask
  omega

 theorem firstTrueCore_queryFree : firstTrueCore.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [OracleBlock.machine,firstTrueCore]

 theorem firstTrueMask_queryFree : firstTrueMask.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ firstTrueCore_queryFree (clear_queryFree _))

 noncomputable def firstTrueOn {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : OracleBlock k := rename firstTrueMask φ

 theorem firstTrueOn_executes {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s t : Store k) (mask : BitString)
    (hs : s∘φ=searchStore mask 0 [] [])
    (ht : t∘φ=searchStore mask (seekPos mask) [] [seekFound mask])
    (hf : ∀ j, (∀ i, φ i≠j) → t j=s j) :
    ∃ cost, (firstTrueOn φ).Executes g s t cost ∧ cost ≤ 8*mask.length+9 := by
  obtain ⟨cost,h,hb⟩ := firstTrueMask_executes g mask
  exact ⟨cost,rename_executes_to _ φ g h hs ht hf,hb⟩

end HiddenCircuits.Approximation.SelfReduction.Runtime
