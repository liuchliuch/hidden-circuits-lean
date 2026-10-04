import HiddenCircuits.Complexity.GraphVerifier.MatchingPairRowRuntime

/-! Actual nested unary-clock matrix/certificate scan, with a displayed quartic cost bound. -/
namespace HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
open OracleBlock Runtime

def pairRowsEmbedding : Fin 17 ↪ Fin 18 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun z : Fin 18 => z.val) h)

noncomputable def pairRowsBody : OracleBlock 17 :=
  seq (copyOn 0 16 14 (by decide) (by decide) (by decide))
    (seq (rename pairRowBlock pairRowsEmbedding) (seq (clear 2) (push 1 true)))
noncomputable def pairRowsBlock : OracleBlock 17 := whilePop 17 pairRowsBody pairRowsBody
noncomputable def allPairsBlock : OracleBlock 17 :=
  seq (copyOn 0 17 14 (by decide) (by decide) (by decide)) pairRowsBlock

def scanStore (n i j : ℕ) (payload witness : BitString) (a : Bool) (inner outer : BitString) : Store 17 := fun r =>
  if h:r.val<17 then pairRowStore n i j payload witness a inner ⟨r.val,h⟩ else outer

def pairRowsCostBound (n : ℕ) : ℕ := n*pairCostBound n+11*n+11

def pairRowsValue (n : ℕ) (payload witness : BitString) : ℕ → ℕ → Bool → Bool
  | _,0,a => a
  | i,m+1,a => pairRowsValue n payload witness (i+1) m (pairRowValue n payload witness i 0 n a)

 theorem pairRowsBody_executes (g : BitString → ℕ) (n i : ℕ) (payload witness outer : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n*n≤witness.length) (hi : i<n) :
    ∃ cost, pairRowsBody.Executes g (scanStore n i 0 payload witness a [] outer)
      (scanStore n (i+1) 0 payload witness (pairRowValue n payload witness i 0 n a) [] outer) cost ∧
      cost≤pairRowsCostBound n := by
  let s₀ := scanStore n i 0 payload witness a [] outer
  let s₁ := scanStore n i 0 payload witness a (List.replicate n true) outer
  let b := pairRowValue n payload witness i 0 n a
  let s₂ := scanStore n i n payload witness b [] outer
  let s₃ := scanStore n i 0 payload witness b [] outer
  let s₄ := scanStore n (i+1) 0 payload witness b [] outer
  have h₁ : (copyOn (0:Fin 18) 16 14 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*n+2) := by
    convert copyOn_executes g (0:Fin 18) 16 14 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext r;fin_cases r <;> simp [s₀,s₁,scanStore,pairRowStore,pairStore]
    · simp [s₀,scanStore,pairRowStore,pairStore]
  obtain ⟨c,hc,hcb⟩ := pairRow_executes g n i 0 n payload witness a hp hw hi (by omega)
  have h₂ : (rename pairRowBlock pairRowsEmbedding).Executes g s₁ s₂ c := by
    apply rename_executes_to pairRowBlock pairRowsEmbedding g hc
    · funext r;fin_cases r <;> rfl
    · simp only [Nat.zero_add]
      funext r;fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact False.elim (hr 2 rfl) | exact False.elim (hr 5 rfl) | exact False.elim (hr 16 rfl)
  have h₃ : (clear (2:Fin 18)).Executes g s₂ s₃ (n+1) := by
    convert clear_executes g (2:Fin 18) s₂ using 1
    · funext r;fin_cases r <;> rfl
    · simp [s₂,scanStore,pairRowStore,pairStore]
  have h₄ : (push (1:Fin 18) true).Executes g s₃ s₄ 1 := by
    convert push_executes g (1:Fin 18) true s₃ using 1
    funext r;fin_cases r <;> simp [s₃,s₄,scanStore,pairRowStore,pairStore,List.replicate_succ]
  refine ⟨(5*n+2)+(c+((n+1)+1+2)+2)+2,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)),?_⟩
  unfold pairRowsCostBound
  nlinarith

 theorem pairRows_loop (g : BitString → ℕ) (n i m : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n*n≤witness.length) (him : i+m≤n) :
    ∃ cost, WhileExecution (17:Fin 18) pairRowsBody pairRowsBody g
      (scanStore n i 0 payload witness a [] (List.replicate m true))
      (scanStore n (i+m) 0 payload witness (pairRowsValue n payload witness i m a) [] []) cost ∧
      cost≤m*(pairRowsCostBound n+2)+1 := by
  induction m generalizing i a with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [pairRowsValue] using (WhileExecution.empty (stack:=(17:Fin 18)) (B:=pairRowsBody) (C:=pairRowsBody)
      (g:=g) (scanStore n i 0 payload witness a [] []) rfl)
  | succ m ih =>
    have hi : i<n := by omega
    obtain ⟨c,hc,hcb⟩ := pairRowsBody_executes g n i payload witness (List.replicate m true) a hp hw hi
    obtain ⟨t,ht,htb⟩ := ih (i+1) (pairRowValue n payload witness i 0 n a) (by omega)
    have he : Function.update (scanStore n i 0 payload witness a [] (List.replicate (m+1) true)) (17:Fin 18)
        (List.replicate m true)=scanStore n i 0 payload witness a [] (List.replicate m true) := by
      funext r;fin_cases r <;> rfl
    have hc' : pairRowsBody.Executes g
        (Function.update (scanStore n i 0 payload witness a [] (List.replicate (m+1) true)) (17:Fin 18) (List.replicate m true))
        (scanStore n (i+1) 0 payload witness (pairRowValue n payload witness i 0 n a) [] (List.replicate m true)) c := by rwa [he]
    have hend : (i+1)+m=i+(m+1) := by omega
    rw [hend] at ht
    refine ⟨1+c+1+t,?_,?_⟩
    · exact WhileExecution.one
        (show scanStore n i 0 payload witness a [] (List.replicate (m+1) true) 17=true::List.replicate m true from rfl) hc' ht
    · nlinarith

 theorem pairRowsValue_all (n : ℕ) (payload witness : BitString) (i m : ℕ) (a : Bool) :
    pairRowsValue n payload witness i m a=
      (a && (List.range' i m).all (fun r => (List.range n).all (entryFlag n payload witness r))) := by
  induction m generalizing i a with
  | zero => simp [pairRowsValue]
  | succ m ih => simp [pairRowsValue,pairRowValue_all,ih,List.range'_succ,← List.range_eq_range',Bool.and_assoc]

/-- One fixed finite machine validates all n² pairs. n is read from its unary input,
never substituted into the program code, and every elementary lookup is charged. -/
theorem allPairs_executes (g : BitString → ℕ) (n : ℕ) (payload witness : BitString) (a : Bool)
    (hp : payload.length=n*n) (hw : n*n≤witness.length) :
    ∃ cost, allPairsBlock.Executes g (scanStore n 0 0 payload witness a [] [])
      (scanStore n n 0 payload witness (a && scanPairs n payload witness) [] []) cost ∧
      cost≤56*n^4+118*n^3+145*n^2+18*n+5 := by
  have h₁ : (copyOn (0:Fin 18) 17 14 (by decide) (by decide) (by decide)).Executes g
      (scanStore n 0 0 payload witness a [] []) (scanStore n 0 0 payload witness a [] (List.replicate n true))
      (5*n+2) := by
    convert copyOn_executes g (0:Fin 18) 17 14 (by decide) (by decide) (by decide)
      (scanStore n 0 0 payload witness a [] []) rfl using 1
    · funext r;fin_cases r <;> simp [scanStore,pairRowStore,pairStore]
    · simp [scanStore,pairRowStore,pairStore]
  obtain ⟨c,hc,hcb⟩ := pairRows_loop g n 0 n payload witness a hp hw (by omega)
  have h₂ := whilePop_executes _ _ _ g hc
  have hval : pairRowsValue n payload witness 0 n a=(a && scanPairs n payload witness) := by
    simpa [scanPairs,← List.range_eq_range'] using pairRowsValue_all n payload witness 0 n a
  refine ⟨5*n+2+c+2,?_,?_⟩
  · simpa only [Nat.zero_add,hval] using seq_executes _ _ g h₁ h₂
  · unfold pairRowsCostBound pairCostBound at hcb
    nlinarith

 theorem pairRowsBody_queryFree : pairRowsBody.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ pairRow_queryFree) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
 theorem allPairs_queryFree : allPairsBlock.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (whilePop_queryFree _ _ _ pairRowsBody_queryFree pairRowsBody_queryFree)

end HiddenCircuits.Complexity.GraphVerifier.MatchingRuntime
