import HiddenCircuits.Complexity.GraphVerifier.PairRuntime

/-! Actual unary-clock row traversal, invoking the fully checked pair program at each column. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def rowEmbedding : Fin 16 ↪ Fin 17 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun z : Fin 17 => z.val) h)

noncomputable def rowBody : OracleBlock 16 := seq (rename pairCheckBlock rowEmbedding) (push 2 true)
noncomputable def rowBlock : OracleBlock 16 := whilePop 16 rowBody rowBody

def rowStore (n i j : ℕ) (payload witness : BitString) (a : Bool) (clock : BitString) : Store 16 := fun r =>
  if h:r.val<16 then pairStore n i j payload witness [a] [] [] [] [] [] [] ⟨r.val,h⟩ else clock

def pairCostBound (n : ℕ) : ℕ := 28*n^2+88*n+106

def rowValue (n : ℕ) (payload witness : BitString) (i : ℕ) : ℕ → ℕ → Bool → Bool
  | _,0,a => a
  | j,m+1,a => rowValue n payload witness i (j+1) m (a && entryFlag n payload witness i j)

 theorem rowBody_executes (g : BitString → ℕ) (n i j : ℕ) (payload witness clock : BitString)
    (a : Bool) (hp : payload.length=n*n) (hw : n≤witness.length) (hi : i<n) (hj : j<n) :
    ∃ cost, rowBody.Executes g (rowStore n i j payload witness a clock)
      (rowStore n i (j+1) payload witness (a && entryFlag n payload witness i j) clock) cost ∧
      cost≤pairCostBound n+3 := by
  obtain ⟨c,hc,hb⟩ := pairCheck_executes g n i j payload witness a hp hw hi hj
  have h₁ : (rename pairCheckBlock rowEmbedding).Executes g (rowStore n i j payload witness a clock)
      (rowStore n i j payload witness (a && entryFlag n payload witness i j) clock) c := by
    apply rename_executes_to pairCheckBlock rowEmbedding g hc
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact False.elim (hr 5 rfl)
  have h₂ : (push (2:Fin 17) true).Executes g
      (rowStore n i j payload witness (a && entryFlag n payload witness i j) clock)
      (rowStore n i (j+1) payload witness (a && entryFlag n payload witness i j) clock) 1 := by
    have hh := push_executes g (2:Fin 17) true
      (rowStore n i j payload witness (a && entryFlag n payload witness i j) clock)
    convert hh using 1
    funext r;fin_cases r <;> simp [rowStore,pairStore,List.replicate_succ]
  exact ⟨c+1+2,seq_executes _ _ g h₁ h₂,by unfold pairCostBound; omega⟩

/-- An actual row loop visits precisely j,j+1,...,j+m-1 and empties its clock. -/
theorem row_loop (g : BitString → ℕ) (n i j m : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n≤witness.length) (hi : i<n) (hjm : j+m≤n) :
    ∃ cost, WhileExecution (16:Fin 17) rowBody rowBody g (rowStore n i j payload witness a (List.replicate m true))
      (rowStore n i (j+m) payload witness (rowValue n payload witness i j m a) []) cost ∧
      cost≤m*(pairCostBound n+5)+1 := by
  induction m generalizing j a with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [rowValue] using (WhileExecution.empty (stack:=(16:Fin 17)) (B:=rowBody) (C:=rowBody)
      (g:=g) (rowStore n i j payload witness a []) rfl)
  | succ m ih =>
    have hj : j<n := by omega
    obtain ⟨c,hc,hcb⟩ := rowBody_executes g n i j payload witness (List.replicate m true) a hp hw hi hj
    obtain ⟨t,ht,htb⟩ := ih (j+1) (a && entryFlag n payload witness i j) (by omega)
    have he : Function.update (rowStore n i j payload witness a (List.replicate (m+1) true)) (16:Fin 17)
        (List.replicate m true)=rowStore n i j payload witness a (List.replicate m true) := by
      funext r;fin_cases r <;> rfl
    have hc' : rowBody.Executes g
        (Function.update (rowStore n i j payload witness a (List.replicate (m+1) true)) (16:Fin 17) (List.replicate m true))
        (rowStore n i (j+1) payload witness (a && entryFlag n payload witness i j) (List.replicate m true)) c := by rwa [he]
    have hend : (j+1)+m=j+(m+1) := by omega
    rw [hend] at ht
    refine ⟨1+c+1+t,?_,?_⟩
    · exact WhileExecution.one
        (show rowStore n i j payload witness a (List.replicate (m+1) true) 16=true::List.replicate m true from rfl) hc' ht
    · nlinarith

/-- The row-loop trace is executed by its actual fixed finite instruction graph. -/
theorem row_executes (g : BitString → ℕ) (n i j m : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n≤witness.length) (hi : i<n) (hjm : j+m≤n) :
    ∃ cost, rowBlock.Executes g (rowStore n i j payload witness a (List.replicate m true))
      (rowStore n i (j+m) payload witness (rowValue n payload witness i j m a) []) cost ∧
      cost≤m*(pairCostBound n+5)+1 := by
  obtain ⟨c,hc,hb⟩ := row_loop g n i j m payload witness a hp hw hi hjm
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩

 theorem rowValue_all (n : ℕ) (payload witness : BitString) (i j m : ℕ) (a : Bool) :
    rowValue n payload witness i j m a=(a && (List.range' j m).all (entryFlag n payload witness i)) := by
  induction m generalizing j a with
  | zero => simp [rowValue]
  | succ m ih => simp [rowValue,List.range'_succ,ih,Bool.and_assoc]

 theorem rowBody_queryFree : rowBody.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ pairCheck_queryFree) (push_queryFree _ _)

 theorem row_queryFree : rowBlock.QueryFree := whilePop_queryFree _ _ _ rowBody_queryFree rowBody_queryFree

end HiddenCircuits.Complexity.GraphVerifier.Runtime
