import HiddenCircuits.Complexity.GraphVerifier.MatchingPairRuntime

/-! Actual unary-clock pairRow traversal, invoking the fully checked pair program at each column. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open OracleBlock Runtime

def pairRowEmbedding : Fin 16 ↪ Fin 17 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun z : Fin 17 => z.val) h)

noncomputable def pairRowBody : OracleBlock 16 := seq (rename pairCheckBlock pairRowEmbedding) (push 2 true)
noncomputable def pairRowBlock : OracleBlock 16 := whilePop 16 pairRowBody pairRowBody

def pairRowStore (n i j : ℕ) (payload witness : BitString) (a : Bool) (clock : BitString) : Store 16 := fun r =>
  if h:r.val<16 then pairStore n i j payload witness [a] [] [] [] [] [] [] ⟨r.val,h⟩ else clock

def pairCostBound (n : ℕ) : ℕ := 56*n^2+118*n+134

def pairRowValue (n : ℕ) (payload witness : BitString) (i : ℕ) : ℕ → ℕ → Bool → Bool
  | _,0,a => a
  | j,m+1,a => pairRowValue n payload witness i (j+1) m (a && entryFlag n payload witness i j)

 theorem pairRowBody_executes (g : BitString → ℕ) (n i j : ℕ) (payload witness clock : BitString)
    (a : Bool) (hp : payload.length=n*n) (hw : n*n≤witness.length) (hi : i<n) (hj : j<n) :
    ∃ cost, pairRowBody.Executes g (pairRowStore n i j payload witness a clock)
      (pairRowStore n i (j+1) payload witness (a && entryFlag n payload witness i j) clock) cost ∧
      cost≤pairCostBound n+3 := by
  obtain ⟨c,hc,hb⟩ := pairCheck_executes g n i j payload witness a hp hw hi hj
  have h₁ : (rename pairCheckBlock pairRowEmbedding).Executes g (pairRowStore n i j payload witness a clock)
      (pairRowStore n i j payload witness (a && entryFlag n payload witness i j) clock) c := by
    apply rename_executes_to pairCheckBlock pairRowEmbedding g hc
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact False.elim (hr 5 rfl)
  have h₂ : (push (2:Fin 17) true).Executes g
      (pairRowStore n i j payload witness (a && entryFlag n payload witness i j) clock)
      (pairRowStore n i (j+1) payload witness (a && entryFlag n payload witness i j) clock) 1 := by
    have hh := push_executes g (2:Fin 17) true
      (pairRowStore n i j payload witness (a && entryFlag n payload witness i j) clock)
    convert hh using 1
    funext r;fin_cases r <;> simp [pairRowStore,pairStore,List.replicate_succ]
  exact ⟨c+1+2,seq_executes _ _ g h₁ h₂,by unfold pairCostBound; omega⟩

/-- An actual pairRow loop visits precisely j,j+1,...,j+m-1 and empties its clock. -/
theorem pairRow_loop (g : BitString → ℕ) (n i j m : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n*n≤witness.length) (hi : i<n) (hjm : j+m≤n) :
    ∃ cost, WhileExecution (16:Fin 17) pairRowBody pairRowBody g (pairRowStore n i j payload witness a (List.replicate m true))
      (pairRowStore n i (j+m) payload witness (pairRowValue n payload witness i j m a) []) cost ∧
      cost≤m*(pairCostBound n+5)+1 := by
  induction m generalizing j a with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [pairRowValue] using (WhileExecution.empty (stack:=(16:Fin 17)) (B:=pairRowBody) (C:=pairRowBody)
      (g:=g) (pairRowStore n i j payload witness a []) rfl)
  | succ m ih =>
    have hj : j<n := by omega
    obtain ⟨c,hc,hcb⟩ := pairRowBody_executes g n i j payload witness (List.replicate m true) a hp hw hi hj
    obtain ⟨t,ht,htb⟩ := ih (j+1) (a && entryFlag n payload witness i j) (by omega)
    have he : Function.update (pairRowStore n i j payload witness a (List.replicate (m+1) true)) (16:Fin 17)
        (List.replicate m true)=pairRowStore n i j payload witness a (List.replicate m true) := by
      funext r;fin_cases r <;> rfl
    have hc' : pairRowBody.Executes g
        (Function.update (pairRowStore n i j payload witness a (List.replicate (m+1) true)) (16:Fin 17) (List.replicate m true))
        (pairRowStore n i (j+1) payload witness (a && entryFlag n payload witness i j) (List.replicate m true)) c := by rwa [he]
    have hend : (j+1)+m=j+(m+1) := by omega
    rw [hend] at ht
    refine ⟨1+c+1+t,?_,?_⟩
    · exact WhileExecution.one
        (show pairRowStore n i j payload witness a (List.replicate (m+1) true) 16=true::List.replicate m true from rfl) hc' ht
    · nlinarith

/-- The pairRow-loop trace is executed by its actual fixed finite instruction graph. -/
theorem pairRow_executes (g : BitString → ℕ) (n i j m : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n*n≤witness.length) (hi : i<n) (hjm : j+m≤n) :
    ∃ cost, pairRowBlock.Executes g (pairRowStore n i j payload witness a (List.replicate m true))
      (pairRowStore n i (j+m) payload witness (pairRowValue n payload witness i j m a) []) cost ∧
      cost≤m*(pairCostBound n+5)+1 := by
  obtain ⟨c,hc,hb⟩ := pairRow_loop g n i j m payload witness a hp hw hi hjm
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩

 theorem pairRowValue_all (n : ℕ) (payload witness : BitString) (i j m : ℕ) (a : Bool) :
    pairRowValue n payload witness i j m a=(a && (List.range' j m).all (entryFlag n payload witness i)) := by
  induction m generalizing j a with
  | zero => simp [pairRowValue]
  | succ m ih => simp [pairRowValue,List.range'_succ,ih,Bool.and_assoc]

 theorem pairRowBody_queryFree : pairRowBody.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ pairCheck_queryFree) (push_queryFree _ _)

 theorem pairRow_queryFree : pairRowBlock.QueryFree := whilePop_queryFree _ _ _ pairRowBody_queryFree pairRowBody_queryFree

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
