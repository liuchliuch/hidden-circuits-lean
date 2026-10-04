import HiddenCircuits.Complexity.GraphVerifier.RowRuntime

/-! Actual nested unary-clock matrix/certificate scan, with a displayed quartic cost bound. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def rowsEmbedding : Fin 17 ↪ Fin 18 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun z : Fin 18 => z.val) h)

noncomputable def rowsBody : OracleBlock 17 :=
  seq (copyOn 0 16 14 (by decide) (by decide) (by decide))
    (seq (rename rowBlock rowsEmbedding) (seq (clear 2) (push 1 true)))
noncomputable def rowsBlock : OracleBlock 17 := whilePop 17 rowsBody rowsBody
noncomputable def allPairsBlock : OracleBlock 17 :=
  seq (copyOn 0 17 14 (by decide) (by decide) (by decide)) rowsBlock

def scanStore (n i j : ℕ) (payload witness : BitString) (a : Bool) (inner outer : BitString) : Store 17 := fun r =>
  if h:r.val<17 then rowStore n i j payload witness a inner ⟨r.val,h⟩ else outer

def rowsCostBound (n : ℕ) : ℕ := n*pairCostBound n+11*n+11

def rowsValue (n : ℕ) (payload witness : BitString) : ℕ → ℕ → Bool → Bool
  | _,0,a => a
  | i,m+1,a => rowsValue n payload witness (i+1) m (rowValue n payload witness i 0 n a)

 theorem rowsBody_executes (g : BitString → ℕ) (n i : ℕ) (payload witness outer : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n≤witness.length) (hi : i<n) :
    ∃ cost, rowsBody.Executes g (scanStore n i 0 payload witness a [] outer)
      (scanStore n (i+1) 0 payload witness (rowValue n payload witness i 0 n a) [] outer) cost ∧
      cost≤rowsCostBound n := by
  let s₀ := scanStore n i 0 payload witness a [] outer
  let s₁ := scanStore n i 0 payload witness a (List.replicate n true) outer
  let b := rowValue n payload witness i 0 n a
  let s₂ := scanStore n i n payload witness b [] outer
  let s₃ := scanStore n i 0 payload witness b [] outer
  let s₄ := scanStore n (i+1) 0 payload witness b [] outer
  have h₁ : (copyOn (0:Fin 18) 16 14 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*n+2) := by
    convert copyOn_executes g (0:Fin 18) 16 14 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext r;fin_cases r <;> simp [s₀,s₁,scanStore,rowStore,pairStore]
    · simp [s₀,scanStore,rowStore,pairStore]
  obtain ⟨c,hc,hcb⟩ := row_executes g n i 0 n payload witness a hp hw hi (by omega)
  have h₂ : (rename rowBlock rowsEmbedding).Executes g s₁ s₂ c := by
    apply rename_executes_to rowBlock rowsEmbedding g hc
    · funext r;fin_cases r <;> rfl
    · simp only [Nat.zero_add]
      funext r;fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact False.elim (hr 2 rfl) | exact False.elim (hr 5 rfl) | exact False.elim (hr 16 rfl)
  have h₃ : (clear (2:Fin 18)).Executes g s₂ s₃ (n+1) := by
    convert clear_executes g (2:Fin 18) s₂ using 1
    · funext r;fin_cases r <;> rfl
    · simp [s₂,scanStore,rowStore,pairStore]
  have h₄ : (push (1:Fin 18) true).Executes g s₃ s₄ 1 := by
    convert push_executes g (1:Fin 18) true s₃ using 1
    funext r;fin_cases r <;> simp [s₃,s₄,scanStore,rowStore,pairStore,List.replicate_succ]
  refine ⟨(5*n+2)+(c+((n+1)+1+2)+2)+2,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  unfold rowsCostBound
  nlinarith

 theorem rows_loop (g : BitString → ℕ) (n i m : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n≤witness.length) (him : i+m≤n) :
    ∃ cost, WhileExecution (17:Fin 18) rowsBody rowsBody g
      (scanStore n i 0 payload witness a [] (List.replicate m true))
      (scanStore n (i+m) 0 payload witness (rowsValue n payload witness i m a) [] []) cost ∧
      cost≤m*(rowsCostBound n+2)+1 := by
  induction m generalizing i a with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [rowsValue] using (WhileExecution.empty (stack:=(17:Fin 18)) (B:=rowsBody) (C:=rowsBody)
      (g:=g) (scanStore n i 0 payload witness a [] []) rfl)
  | succ m ih =>
    have hi : i<n := by omega
    obtain ⟨c,hc,hcb⟩ := rowsBody_executes g n i payload witness (List.replicate m true) a hp hw hi
    obtain ⟨t,ht,htb⟩ := ih (i+1) (rowValue n payload witness i 0 n a) (by omega)
    have he : Function.update (scanStore n i 0 payload witness a [] (List.replicate (m+1) true)) (17:Fin 18)
        (List.replicate m true)=scanStore n i 0 payload witness a [] (List.replicate m true) := by
      funext r;fin_cases r <;> rfl
    have hc' : rowsBody.Executes g
        (Function.update (scanStore n i 0 payload witness a [] (List.replicate (m+1) true)) (17:Fin 18) (List.replicate m true))
        (scanStore n (i+1) 0 payload witness (rowValue n payload witness i 0 n a) [] (List.replicate m true)) c := by rwa [he]
    have hend : (i+1)+m=i+(m+1) := by omega
    rw [hend] at ht
    refine ⟨1+c+1+t,?_,?_⟩
    · exact WhileExecution.one
        (show scanStore n i 0 payload witness a [] (List.replicate (m+1) true) 17=true::List.replicate m true from rfl) hc' ht
    · nlinarith

 theorem rowsValue_all (n : ℕ) (payload witness : BitString) (i m : ℕ) (a : Bool) :
    rowsValue n payload witness i m a=
      (a && (List.range' i m).all (fun r => (List.range n).all (entryFlag n payload witness r))) := by
  induction m generalizing i a with
  | zero => simp [rowsValue]
  | succ m ih => simp [rowsValue,rowValue_all,ih,List.range'_succ,← List.range_eq_range',Bool.and_assoc]

/-- One fixed finite machine validates all n² pairs. n is read from its unary input,
never substituted into the program code, and every elementary lookup is charged. -/
theorem allPairs_executes (g : BitString → ℕ) (n : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n≤witness.length) :
    ∃ cost, allPairsBlock.Executes g (scanStore n 0 0 payload witness a [] [])
      (scanStore n n 0 payload witness (a && scanPairs n payload witness) [] []) cost ∧
      cost≤28*n^4+88*n^3+117*n^2+18*n+5 := by
  have h₁ : (copyOn (0:Fin 18) 17 14 (by decide) (by decide) (by decide)).Executes g
      (scanStore n 0 0 payload witness a [] []) (scanStore n 0 0 payload witness a [] (List.replicate n true))
      (5*n+2) := by
    convert copyOn_executes g (0:Fin 18) 17 14 (by decide) (by decide) (by decide)
      (scanStore n 0 0 payload witness a [] []) rfl using 1
    · funext r;fin_cases r <;> simp [scanStore,rowStore,pairStore]
    · simp [scanStore,rowStore,pairStore]
  obtain ⟨c,hc,hcb⟩ := rows_loop g n 0 n payload witness a hp hw (by omega)
  have h₂ := whilePop_executes _ _ _ g hc
  have hval : rowsValue n payload witness 0 n a=(a && scanPairs n payload witness) := by
    simpa [scanPairs,← List.range_eq_range'] using rowsValue_all n payload witness 0 n a
  refine ⟨5*n+2+c+2,?_,?_⟩
  · simpa only [Nat.zero_add,hval] using seq_executes _ _ g h₁ h₂
  · unfold rowsCostBound pairCostBound at hcb
    nlinarith

 theorem rowsBody_queryFree : rowsBody.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ row_queryFree) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
 theorem allPairs_queryFree : allPairsBlock.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (whilePop_queryFree _ _ _ rowsBody_queryFree rowsBody_queryFree)

end HiddenCircuits.Complexity.GraphVerifier.Runtime
