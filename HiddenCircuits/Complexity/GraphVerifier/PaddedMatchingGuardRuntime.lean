import HiddenCircuits.Complexity.GraphVerifier.PrepareRuntime
import HiddenCircuits.Complexity.GraphVerifier.SquarePadding
import HiddenCircuits.Complexity.GraphVerifier.SquareAtLeast
import HiddenCircuits.Complexity.GraphVerifier.PaddedMatchingSemantics
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! Genuine raw-input guard for the squared-size matching witness. -/
namespace HiddenCircuits.Complexity.GraphVerifier.PaddedMatchingRuntime
open OracleBlock Runtime

def prepareWideEmbedding : Fin 15 ↪ Fin 38 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 38 => z.val) h)

def headerEmbedding : Fin 4 ↪ Fin 38 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 15 else if i.val=2 then 17 else 16
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def certLengthEmbedding : Fin 8 ↪ Fin 38 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 0 else if i.val=2 then 18
    else if i.val=3 then 19 else if i.val=4 then 20 else if i.val=5 then 17 else if i.val=6 then 21 else 22
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def payloadLengthEmbedding : Fin 8 ↪ Fin 38 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 4 else if i.val=2 then 23
    else if i.val=3 then 19 else if i.val=4 then 20 else if i.val=5 then 17 else if i.val=6 then 21 else 22
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def certPaddingEmbedding : Fin 8 ↪ Fin 38 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 0 else if i.val=2 then 24
    else if i.val=3 then 19 else if i.val=4 then 20 else if i.val=5 then 17 else if i.val=6 then 21 else 22
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def guardInputs : List (Fin 38) := [3,7,9,18,23,24]
noncomputable def guardStageBlock : OracleBlock 37 := seq (headerOn headerEmbedding)
  (seq (squareAtLeastOn certLengthEmbedding) (seq (squareLengthOn payloadLengthEmbedding)
    (seq (squarePaddingOn certPaddingEmbedding) (decision 25 guardInputs (fun bs => bs.all id)))))
noncomputable def guardBlock : OracleBlock 37 := seq (rename prepareBlock prepareWideEmbedding) guardStageBlock

def widePrepared (xs a b : BitString) : Store 37 := fun i =>
  if h:i.val<15 then preparedStore xs a b ⟨i.val,h⟩ else []
def guardBits (xs : BitString) (i : Fin 38) : Bool :=
  let x := (parse xs).left
  let w := (parse xs).right
  let q := parse x
  if i.val=3 then (parse xs).ok else if i.val=7 then q.ok else if i.val=9 then q.left.all id
  else if i.val=18 then decide (q.left.length*q.left.length≤w.length)
  else if i.val=23 then decide (q.right.length=q.left.length*q.left.length)
  else (w.drop (q.left.length*q.left.length)).all (fun b => !b)
def headerReady (xs a b : BitString) : Store 37 :=
  Function.update (Function.update (widePrepared xs a b) 15 (List.replicate (parse xs).left.length true))
    16 [(parse xs).left.all id]
def guardReady (xs a b : BitString) : Store 37 :=
  Function.update (Function.update (Function.update (headerReady xs a b) 18 [guardBits xs 18])
    23 [guardBits xs 23]) 24 [guardBits xs 24]
def guardedStore (xs a b : BitString) : Store 37 :=
  Function.update (eraseStore guardInputs (guardReady xs a b)) 25 [guardValue xs]

theorem guardStage_executes (g : BitString → ℕ) (xs a b : BitString) :
    ∃ cost, guardStageBlock.Executes g (widePrepared xs a b) (guardedStore xs a b) cost ∧
      cost≤52*xs.length^2+64*xs.length+122 := by
  let x := (parse xs).left
  let n := (parse x).left.length
  let p := (parse x).right
  let w := (parse xs).right
  let s₀ := widePrepared xs a b
  let s₁ := headerReady xs a b
  let s₂ := Function.update s₁ (18:Fin 38) [guardBits xs 18]
  let s₃ := Function.update s₂ (23:Fin 38) [guardBits xs 23]
  let s₄ := guardReady xs a b
  have h₁ : (headerOn headerEmbedding).Executes g s₀ s₁ (5*x.length+3) :=
    headerOn_executes headerEmbedding g s₀ x (by funext i;fin_cases i <;> rfl)
  obtain ⟨c,hc,hcb⟩ := squareAtLeastOn_executes certLengthEmbedding g s₁ n w
    (by funext i;fin_cases i <;> rfl)
  have h₂ : (squareAtLeastOn certLengthEmbedding).Executes g s₁ s₂ c := hc
  obtain ⟨d,hd,hdb⟩ := squareLengthOn_executes payloadLengthEmbedding g s₂ n p
    (by funext i;fin_cases i <;> rfl)
  have h₃ : (squareLengthOn payloadLengthEmbedding).Executes g s₂ s₃ d := hd
  obtain ⟨e,he,heb⟩ := squarePaddingOn_executes certPaddingEmbedding g s₃ n w
    (by funext i;fin_cases i <;> rfl)
  have h₄ : (squarePaddingOn certPaddingEmbedding).Executes g s₃ s₄ e := he
  have h₅ : (decision (25:Fin 38) guardInputs (fun bs => bs.all id)).Executes g s₄ (guardedStore xs a b) 16 := by
    have hh := decision_executes (25:Fin 38) guardInputs (by decide +kernel) (by decide +kernel)
      (fun bs => bs.all id) (guardBits xs) g s₄ (by
        intro i hi
        simp only [guardInputs,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    have hv : (guardInputs.map (guardBits xs)).all id=guardValue xs := by
      simp [guardInputs,guardBits,guardValue,Bool.and_assoc]
    dsimp only at hh
    rw [hv] at hh
    exact hh
  refine ⟨(5*x.length+3)+(c+(d+(e+16+2)+2)+2)+2,
    seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅))),?_⟩
  have hb := Runtime.guard_data_bounds xs
  have hx := (parse_lengths xs).1
  have hn := Nat.mul_le_mul hb.1 hb.1
  have hxx := Nat.mul_le_mul hx hx
  dsimp [x,n,p,w] at hcb hdb heb ⊢
  nlinarith

theorem guardStage_queryFree : guardStageBlock.QueryFree :=
  seq_queryFree _ _ (headerOn_queryFree _) (seq_queryFree _ _ (squareAtLeastOn_queryFree _)
    (seq_queryFree _ _ (squareLengthOn_queryFree _) (seq_queryFree _ _ (squarePaddingOn_queryFree _)
      (decision_queryFree _ _ _))))

theorem guard_executes (g : BitString → ℕ) (xs : BitString) :
    ∃ a b cost, guardBlock.Executes g (Function.update (fun _ : Fin 38 => ([]:BitString)) 0 xs)
      (guardedStore xs a b) cost ∧ cost≤52*xs.length^2+92*xs.length+158 := by
  obtain ⟨a,b,c,hc,hcb⟩ := prepare_executes g xs
  have h₁ : (rename prepareBlock prepareWideEmbedding).Executes g
      (Function.update (fun _ : Fin 38 => ([]:BitString)) 0 xs) (widePrepared xs a b) c := by
    apply rename_executes_to prepareBlock prepareWideEmbedding g hc
    · funext i;fin_cases i <;> rfl
    · funext i;simp [Function.comp_def,prepareWideEmbedding,widePrepared,i.isLt]
    · intro j hj
      have hi : ¬j.val<15 := by
        intro h;exact hj ⟨j.val,h⟩ (Fin.ext rfl)
      have hj0 : j≠0 := by intro h;subst j;exact hi (by decide)
      simp [widePrepared,hi,hj0]
  obtain ⟨d,hd,hdb⟩ := guardStage_executes g xs a b
  exact ⟨a,b,c+d+2,seq_executes _ _ g h₁ hd,by omega⟩

theorem guard_queryFree : guardBlock.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ prepare_queryFree) guardStage_queryFree
end HiddenCircuits.Complexity.GraphVerifier.PaddedMatchingRuntime
