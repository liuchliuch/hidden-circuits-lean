import HiddenCircuits.Complexity.CNFEncoding
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorProduct

/-! Actual canonical CNF dimension extraction, preserving original bytes and payload. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter
open OracleBlock
open BinaryArithmetic (pair_parse_cost)

def dimensionStore (input payload tmp vars flag stream count clause : BitString) : Store 7 := fun i =>
  if i.val=0 then input else if i.val=1 then payload else if i.val=2 then tmp
  else if i.val=3 then vars else if i.val=4 then flag else if i.val=5 then stream
  else if i.val=6 then count else clause

def headerEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 3 else if i.val=2 then 2 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def countEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 5 else if i.val=1 then 7 else if i.val=2 then 2 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def headerParse : OracleBlock 7 := GraphVerifier.Runtime.unpairOn headerEmbedding
noncomputable def clauseParse : OracleBlock 7 := GraphVerifier.Runtime.unpairOn countEmbedding
noncomputable def countBody : OracleBlock 7 :=
  seq clauseParse (seq (clear 7) (seq (clear 4) (push 6 true)))
noncomputable def countLoop : OracleBlock 7 := whilePop 5 countBody countBody

 theorem clauseParse_executes (g : BitString → ℕ) (input payload vars count clause rest : BitString) :
    clauseParse.Executes g (dimensionStore input payload [] vars [] (pairBits clause rest) count [])
      (dimensionStore input payload [] vars [true] rest count clause) (5*clause.length+3) := by
  have hh := GraphVerifier.Runtime.unpairOn_executes countEmbedding g
    (dimensionStore input payload [] vars [] (pairBits clause rest) count [])
    (dimensionStore input payload [] vars [true] rest count clause) (pairBits clause rest)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl))
  convert hh using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

 theorem countBody_executes (g : BitString → ℕ) (input payload vars count clause rest : BitString) :
    countBody.Executes g (dimensionStore input payload [] vars [] (pairBits clause rest) count [])
      (dimensionStore input payload [] vars [] rest (true::count) []) (6*clause.length+13) := by
  let s₁ := dimensionStore input payload [] vars [true] rest count clause
  let s₂ := dimensionStore input payload [] vars [true] rest count []
  let s₃ := dimensionStore input payload [] vars [] rest count []
  let s₄ := dimensionStore input payload [] vars [] rest (true::count) []
  have h₁ : (clear (7:Fin 8)).Executes g s₁ s₂ (clause.length+1) := by
    convert clear_executes g (7:Fin 8) s₁ using 1
    funext i;fin_cases i <;> rfl
  have h₂ : (clear (4:Fin 8)).Executes g s₂ s₃ 2 := by
    convert clear_executes g (4:Fin 8) s₂ using 1
    funext i;fin_cases i <;> rfl
  have h₃ : (push (6:Fin 8) true).Executes g s₃ s₄ 1 := by
    convert push_executes g (6:Fin 8) true s₃ using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g (clauseParse_executes g input payload vars count clause rest)
    (seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃)) using 1 <;> omega

 theorem count_loop (g : BitString → ℕ) (input payload vars : BitString) (cs : List BitString) (c : ℕ) :
    WhileExecution (5:Fin 8) countBody countBody g
      (dimensionStore input payload [] vars [] (encodeBitList cs) (List.replicate c true) [])
      (dimensionStore input payload [] vars [] [] (List.replicate (c+cs.length) true) [])
      (6*(cs.map List.length).sum+15*cs.length+1) := by
  induction cs generalizing c with
  | nil => simpa [encodeBitList] using (WhileExecution.empty
      (stack := (5:Fin 8)) (B := countBody) (C := countBody) (g := g)
      (dimensionStore input payload [] vars [] [] (List.replicate c true) []) rfl)
  | cons a cs ih =>
    have hb := countBody_executes g input payload vars (List.replicate c true) a (encodeBitList cs)
    have ht := ih (c+1)
    have he : Function.update (dimensionStore input payload [] vars [] (encodeBitList (a::cs)) (List.replicate c true) []) (5:Fin 8)
        (pairBits a (encodeBitList cs))=dimensionStore input payload [] vars [] (pairBits a (encodeBitList cs)) (List.replicate c true) [] := by
      funext i;fin_cases i <;> rfl
    have hh := WhileExecution.one
      (stack := (5:Fin 8)) (B := countBody) (C := countBody) (g := g)
      (show dimensionStore input payload [] vars [] (encodeBitList (a::cs)) (List.replicate c true) [] 5=true::pairBits a (encodeBitList cs) from rfl)
      (by rw [he];exact hb) (by simpa [List.replicate_succ] using ht)
    convert hh using 1 <;> simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] <;> omega

 theorem countLoop_executes (g : BitString → ℕ) (input payload vars : BitString) (cs : List BitString) :
    countLoop.Executes g (dimensionStore input payload [] vars [] (encodeBitList cs) [] [])
      (dimensionStore input payload [] vars [] [] (List.replicate cs.length true) [])
      (6*(cs.map List.length).sum+15*cs.length+1) := by
  simpa using whilePop_executes _ _ _ g (count_loop g input payload vars cs 0)

noncomputable def dimensionsBlock : OracleBlock 7 :=
  seq (copyOn 0 1 2 (by decide) (by decide) (by decide))
    (seq headerParse (seq (clear 4)
      (seq (copyOn 1 5 2 (by decide) (by decide) (by decide)) countLoop)))

 theorem headerParse_executes (g : BitString → ℕ) (input vars payload : BitString) :
    headerParse.Executes g (dimensionStore input (pairBits vars payload) [] [] [] [] [] [])
      (dimensionStore input payload [] vars [true] [] [] []) (5*vars.length+3) := by
  have hh := GraphVerifier.Runtime.unpairOn_executes headerEmbedding g
    (dimensionStore input (pairBits vars payload) [] [] [] [] [] [])
    (dimensionStore input payload [] vars [true] [] [] []) (pairBits vars payload)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl))
  convert hh using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

 theorem dimensions_executes (g : BitString → ℕ) (vars : BitString) (cs : List BitString) :
    ∃ cost, dimensionsBlock.Executes g (dimensionStore (pairBits vars (encodeBitList cs)) [] [] [] [] [] [] [])
      (dimensionStore (pairBits vars (encodeBitList cs)) (encodeBitList cs) [] vars [] [] (List.replicate cs.length true) []) cost ∧
      cost≤30*(pairBits vars (encodeBitList cs)).length+30 := by
  let x := pairBits vars (encodeBitList cs)
  let p := encodeBitList cs
  let s₀ := dimensionStore x [] [] [] [] [] [] []
  let s₁ := dimensionStore x x [] [] [] [] [] []
  let s₂ := dimensionStore x p [] vars [true] [] [] []
  let s₃ := dimensionStore x p [] vars [] [] [] []
  let s₄ := dimensionStore x p [] vars [] p [] []
  have h₁ : (copyOn (0:Fin 8) 1 2 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*x.length+2) := by
    convert copyOn_executes g (0:Fin 8) 1 2 (by decide) (by decide) (by decide) s₀ rfl using 1
    funext i;fin_cases i <;> simp [s₀,s₁,dimensionStore]
  have h₂ := headerParse_executes g x vars p
  have h₃ : (clear (4:Fin 8)).Executes g s₂ s₃ 2 := by
    convert clear_executes g (4:Fin 8) s₂ using 1
    funext i;fin_cases i <;> rfl
  have h₄ : (copyOn (1:Fin 8) 5 2 (by decide) (by decide) (by decide)).Executes g s₃ s₄ (5*p.length+2) := by
    convert copyOn_executes g (1:Fin 8) 5 2 (by decide) (by decide) (by decide) s₃ rfl using 1
    funext i;fin_cases i <;> simp [s₃,s₄,dimensionStore]
  have hh := seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃
    (seq_executes _ _ g h₄ (countLoop_executes g x p vars cs))))
  refine ⟨_,hh,?_⟩
  simp only [x,p,pairBits_length,encodeBitList_length]
  omega

 theorem dimensions_cnf (g : BitString → ℕ) {n m : ℕ} (F : CNF n m) :
    ∃ cost, dimensionsBlock.Executes g (dimensionStore F.bits [] [] [] [] [] [] [])
      (dimensionStore F.bits (encodeBitList ((List.ofFn F.clause).map CNF.clauseBits)) [] (List.replicate n true) [] [] (List.replicate m true) []) cost ∧
      cost≤30*F.bits.length+30 := by
  simpa [CNF.bits] using dimensions_executes g (List.replicate n true) ((List.ofFn F.clause).map CNF.clauseBits)

 theorem dimensions_queryFree : dimensionsBlock.QueryFree := by
  have hp : clauseParse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have hb : countBody.QueryFree := seq_queryFree _ _ hp
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
  have hl : countLoop.QueryFree := whilePop_queryFree _ _ _ hb hb
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
      (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) hl)))

end HiddenCircuits.Complexity.CNFCloneEmitter
