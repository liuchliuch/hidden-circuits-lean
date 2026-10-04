import HiddenCircuits.Circuit.Runtime.SpectralTargetsCell

/-! Actual nested decreasing unary clocks emit the full triangular target stream. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTargets
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic

def state (g : ℕ) (mode : Bool) (inner outer out : BitString) : Store 8 := fun i =>
  if i.val=0 then List.replicate g true else if i.val=1 then [mode] else if i.val=3 then inner
  else if i.val=7 then outer else if i.val=8 then out else []

def cellEmbedding : Fin 6 ↪ Fin 9 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 1 else if i.val=2 then 8
    else if i.val=3 then 4 else if i.val=4 then 5 else 6
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def rowCell : OracleBlock 8 := rename cell cellEmbedding
noncomputable def rowProgram : OracleBlock 8 := whilePop 3 rowCell rowCell

theorem rowCell_executes (oracle : BitString → ℕ) (g r : ℕ) (mode : Bool) (outer out : BitString) :
    ∃ t, rowCell.Executes oracle (state g mode (List.replicate r true) outer out)
      (state g mode (List.replicate r true) outer ((wordChunk (signedBits ((base mode)^r))).reverse++out)) t ∧ t≤6*r+34 := by
  obtain ⟨t,ht,hb⟩ := cell_executes oracle r mode out
  refine ⟨t,?_,hb⟩
  apply rename_executes_to cell cellEmbedding oracle ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 2 rfl)

theorem row_execution (oracle : BitString → ℕ) (g n : ℕ) (mode : Bool) (outer out : BitString) :
    ∃ t, WhileExecution (3:Fin 9) rowCell rowCell oracle (state g mode (List.replicate n true) outer out)
      (state g mode [] outer ((encodeBitList ((row mode n).map signedBits)).reverse++out)) t ∧ t≤n*(6*n+36)+1 := by
  induction n generalizing out with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [row,encodeBitList] using (WhileExecution.empty (stack:=(3:Fin 9)) (B:=rowCell) (C:=rowCell)
      (g:=oracle) (state g mode [] outer out) rfl)
  | succ n ih =>
    obtain ⟨c,hc,hcb⟩ := rowCell_executes oracle g n mode outer out
    obtain ⟨t,ht,htb⟩ := ih ((wordChunk (signedBits ((base mode)^n))).reverse++out)
    have hs : Function.update (state g mode (List.replicate (n+1) true) outer out) (3:Fin 9)
        (List.replicate n true)=state g mode (List.replicate n true) outer out := by
      funext i;fin_cases i <;> rfl
    rw [←hs] at hc
    have hh := WhileExecution.one
      (show state g mode (List.replicate (n+1) true) outer out 3=true::List.replicate n true from rfl) hc ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa [row,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc] using hh
    · nlinarith

theorem rowProgram_executes (oracle : BitString → ℕ) (g n : ℕ) (mode : Bool) (outer out : BitString) :
    ∃ t, rowProgram.Executes oracle (state g mode (List.replicate n true) outer out)
      (state g mode [] outer ((encodeBitList ((row mode n).map signedBits)).reverse++out)) t ∧ t≤n*(6*n+36)+1 := by
  obtain ⟨t,ht,hb⟩ := row_execution oracle g n mode outer out
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩

noncomputable def outerBody : OracleBlock 8 := seq (copyOn 7 3 6 (by decide) (by decide) (by decide))
  (seq (push 3 true) rowProgram)
noncomputable def outerLoop : OracleBlock 8 := whilePop 7 outerBody outerBody

theorem outerBody_executes (oracle : BitString → ℕ) (g n : ℕ) (mode : Bool) (out : BitString) :
    ∃ t, outerBody.Executes oracle (state g mode [] (List.replicate n true) out)
      (state g mode [] (List.replicate n true) ((encodeBitList ((row mode (n+1)).map signedBits)).reverse++out)) t ∧
      t≤(n+1)*(6*(n+1)+36)+5*n+8 := by
  let s₀ := state g mode [] (List.replicate n true) out
  let s₁ := state g mode (List.replicate n true) (List.replicate n true) out
  let s₂ := state g mode (List.replicate (n+1) true) (List.replicate n true) out
  have h₁ : (copyOn (7:Fin 9) 3 6 (by decide) (by decide) (by decide)).Executes oracle s₀ s₁ (5*n+2) := by
    convert copyOn_executes oracle (7:Fin 9) 3 6 (by decide) (by decide) (by decide) s₀ rfl using 1
    · funext i;fin_cases i <;> simp [s₀,s₁,state]
    · simp [s₀,state]
  have h₂ : (push (3:Fin 9) true).Executes oracle s₁ s₂ 1 := by
    convert push_executes oracle (3:Fin 9) true s₁ using 1
    funext i;fin_cases i <;> simp [s₁,s₂,state,List.replicate_succ]
  obtain ⟨t,ht,htb⟩ := rowProgram_executes oracle g (n+1) mode (List.replicate n true) out
  exact ⟨(5*n+2)+(1+t+2)+2,seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ ht),by omega⟩

def outerBound (n : ℕ) : ℕ := n*((n+1)*(6*(n+1)+36)+5*n+10)+1

theorem outer_execution (oracle : BitString → ℕ) (g n : ℕ) (mode : Bool) (out : BitString) :
    ∃ t, WhileExecution (7:Fin 9) outerBody outerBody oracle (state g mode [] (List.replicate n true) out)
      (state g mode [] [] ((encodeBitList ((triangle mode n).map signedBits)).reverse++out)) t ∧ t≤outerBound n := by
  induction n generalizing out with
  | zero =>
    refine ⟨1,?_,by simp [outerBound]⟩
    simpa [triangle,encodeBitList] using (WhileExecution.empty (stack:=(7:Fin 9)) (B:=outerBody) (C:=outerBody)
      (g:=oracle) (state g mode [] [] out) rfl)
  | succ n ih =>
    obtain ⟨c,hc,hcb⟩ := outerBody_executes oracle g n mode out
    obtain ⟨t,ht,htb⟩ := ih ((encodeBitList ((row mode (n+1)).map signedBits)).reverse++out)
    have hs : Function.update (state g mode [] (List.replicate (n+1) true) out) (7:Fin 9)
        (List.replicate n true)=state g mode [] (List.replicate n true) out := by funext i;fin_cases i <;> rfl
    rw [←hs] at hc
    have hh := WhileExecution.one
      (show state g mode [] (List.replicate (n+1) true) out 7=true::List.replicate n true from rfl) hc ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa [triangle,List.map_append,encodeBitList_append,List.reverse_append,List.append_assoc] using hh
    · unfold outerBound at *
      nlinarith

theorem outerLoop_executes (oracle : BitString → ℕ) (g n : ℕ) (mode : Bool) (out : BitString) :
    ∃ t, outerLoop.Executes oracle (state g mode [] (List.replicate n true) out)
      (state g mode [] [] ((encodeBitList ((triangle mode n).map signedBits)).reverse++out)) t ∧ t≤outerBound n := by
  obtain ⟨t,ht,hb⟩ := outer_execution oracle g n mode out
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩

theorem rowProgram_queryFree : rowProgram.QueryFree :=
  whilePop_queryFree _ _ _ (rename_queryFree _ _ cell_queryFree) (rename_queryFree _ _ cell_queryFree)
theorem outerLoop_queryFree : outerLoop.QueryFree := by
  have hb : outerBody.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (push_queryFree _ _) rowProgram_queryFree)
  exact whilePop_queryFree _ _ _ hb hb
end HiddenCircuits.Circuit.Runtime.SpectralTargets
