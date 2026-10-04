import HiddenCircuits.Complexity.GraphVerifier.PrepareRuntime
import HiddenCircuits.Complexity.GraphVerifier.SquareLength
import HiddenCircuits.Complexity.GraphVerifier.PaddingRuntime
import HiddenCircuits.Complexity.GraphVerifier.GuardSemantics
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! Actual raw-input length/padding guard before the bounded graph scan. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def prepareWideEmbedding : Fin 15 ↪ Fin 38 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 38 => z.val) h)

def squareGuardEmbedding : Fin 8 ↪ Fin 38 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 4 else if i.val=2 then 19
    else if i.val=3 then 15 else if i.val=4 then 16 else if i.val=5 then 17 else if i.val=6 then 21 else 22
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def paddingGuardEmbedding : Fin 6 ↪ Fin 38 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 0 else if i.val=2 then 20
    else if i.val=3 then 15 else if i.val=4 then 16 else 17
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def guardInputs : List (Fin 38) := [3,7,9,14,19,20]

noncomputable def guardStageBlock : OracleBlock 37 :=
  seq (squareLengthOn squareGuardEmbedding) (seq (paddingOn paddingGuardEmbedding) (decision 18 guardInputs (fun bs => bs.all id)))
noncomputable def guardBlock : OracleBlock 37 := seq (rename prepareBlock prepareWideEmbedding) guardStageBlock

def widePrepared (xs a b : BitString) : Store 37 := fun i =>
  if h:i.val<15 then preparedStore xs a b ⟨i.val,h⟩ else []

def guardBits (xs : BitString) (i : Fin 38) : Bool :=
  let x := (parse xs).left
  let w := (parse xs).right
  let q := parse x
  if i.val=3 then (parse xs).ok else if i.val=7 then q.ok else if i.val=9 then q.left.all id
  else if i.val=14 then decide (x.length=w.length) else if i.val=19 then decide (q.right.length=q.left.length*q.left.length)
  else (w.drop q.left.length).all (fun b => !b)

def guardReady (xs a b : BitString) : Store 37 :=
  Function.update (Function.update (widePrepared xs a b) 19 [guardBits xs 19]) 20 [guardBits xs 20]

def guardedStore (xs a b : BitString) : Store 37 :=
  Function.update (eraseStore guardInputs (guardReady xs a b)) 18 [guardValue xs]

 theorem guardStage_executes (g : BitString → ℕ) (xs a b : BitString) :
    ∃ cost, guardStageBlock.Executes g (widePrepared xs a b) (guardedStore xs a b) cost ∧
      cost≤19*xs.length^2+36*xs.length+71 := by
  let n := (parse (parse xs).left).left.length
  let p := (parse (parse xs).left).right
  let w := (parse xs).right
  let s₀ := widePrepared xs a b
  let s₁ := Function.update s₀ (19:Fin 38) [guardBits xs 19]
  let s₂ := guardReady xs a b
  obtain ⟨c,hc,hcb⟩ := squareLengthOn_executes squareGuardEmbedding g s₀ n p
    (by funext i;fin_cases i <;> rfl)
  have h₁ : (squareLengthOn squareGuardEmbedding).Executes g s₀ s₁ c := hc
  obtain ⟨d,hd,hdb⟩ := paddingOn_executes paddingGuardEmbedding g s₁ n w
    (by funext i;fin_cases i <;> rfl)
  have h₂ : (paddingOn paddingGuardEmbedding).Executes g s₁ s₂ d := hd
  have h₃ : (decision (18:Fin 38) guardInputs (fun bs => bs.all id)).Executes g s₂ (guardedStore xs a b) 16 := by
    have hh := decision_executes (18:Fin 38) guardInputs (by decide +kernel) (by decide +kernel)
      (fun bs => bs.all id) (guardBits xs) g s₂ (by
        intro i hi
        simp only [guardInputs,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    have he : (guardInputs.map (guardBits xs)).all id=guardValue xs := by
      simp [guardInputs,guardBits,guardValue,Bool.and_assoc]
    dsimp only at hh
    rw [he] at hh
    exact hh
  refine ⟨c+(d+16+2)+2,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃),?_⟩
  have hb := guard_data_bounds xs
  dsimp [n,p,w] at hcb hdb
  have hsq := Nat.mul_le_mul hb.1 hb.1
  nlinarith

 theorem guardStage_queryFree : guardStageBlock.QueryFree :=
  seq_queryFree _ _ (squareLengthOn_queryFree _) (seq_queryFree _ _ (paddingOn_queryFree _) (decision_queryFree _ _ _))

/-- The entire guard is a single actual finite program on ordinary binary input. -/
theorem guard_executes (g : BitString → ℕ) (xs : BitString) :
    ∃ a b cost, guardBlock.Executes g (Function.update (fun _ : Fin 38 => ([]:BitString)) 0 xs)
      (guardedStore xs a b) cost ∧ cost≤19*xs.length^2+64*xs.length+107 := by
  obtain ⟨a,b,c,hc,hcb⟩ := prepare_executes g xs
  have h₁ : (rename prepareBlock prepareWideEmbedding).Executes g
      (Function.update (fun _ : Fin 38 => ([]:BitString)) 0 xs) (widePrepared xs a b) c := by
    apply rename_executes_to prepareBlock prepareWideEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i
      simp [Function.comp_def,prepareWideEmbedding,widePrepared,i.isLt]
    · intro j hj
      have hi : ¬j.val<15 := by
        intro h
        exact hj ⟨j.val,h⟩ (Fin.ext rfl)
      have hj0 : j≠0 := by intro h;subst j;exact hi (by decide)
      simp [widePrepared,hi,hj0]
  obtain ⟨d,hd,hdb⟩ := guardStage_executes g xs a b
  exact ⟨a,b,c+d+2,seq_executes _ _ g h₁ hd,by omega⟩

 theorem guard_queryFree : guardBlock.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ prepare_queryFree) guardStage_queryFree

end HiddenCircuits.Complexity.GraphVerifier.Runtime
