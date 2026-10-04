import HiddenCircuits.Complexity.InitialCellEmitter

/-! The supplied-source initial-row emitter agrees exactly with the dense-index
image of InitialNetwork.sourceClauses. This file also exposes arbitrary-stack
framing and a polynomial in the actual unary operand lengths. -/
namespace HiddenCircuits.Complexity.InitialCellEmitter
open OracleBlock Polynomial

variable {p n k : ℕ}

def sourceIndex : InputSource p → ℕ
  | .constant _ => 0
  | .bit i _ => i.val

noncomputable def program : InputSource p → OracleBlock 4
  | .constant value => constant value
  | .bit _ negate => bit negate

noncomputable def bits (target : ℕ) : InputSource p → BitString
  | .constant value => serializedClause [(target,value)]
  | .bit i negate => bitBits i.val target negate

def cost (target : ℕ) : InputSource p → ℕ
  | .constant _ => 32*target+56
  | .bit i _ => 64*(i.val+target)+215

noncomputable def time : Polynomial ℕ := 64*X+215

theorem program_executes (g : BitString → ℕ) (s : InputSource p)
    (target : ℕ) (stream : BitString) :
    (program s).Executes g (state (sourceIndex s) target 0 0 stream)
      (state (sourceIndex s) target 0 0 ((bits target s).reverse++stream)) (cost target s) := by
  cases s with
  | constant value => exact constant_executes g value 0 target stream
  | bit i negate => exact bit_executes g negate i.val target stream

lemma cost_bound (s : InputSource p) (target : ℕ) :
    cost target s ≤ time.eval (sourceIndex s+target) := by
  cases s <;> simp [cost,time,sourceIndex] <;> omega

lemma program_queryFree (s : InputSource p) : (program s).QueryFree := by
  cases s with
  | constant value => exact constant_queryFree _
  | bit i negate => exact bit_queryFree _

lemma initial_target_val (p n t : ℕ) (v : Fin n) :
    (InitialNetwork.variableEquiv p n t (Sum.inr (0,v))).val = p+v.val := by
  change p+(v.val+n*0) = p+v.val
  omega

lemma input_val (p n t : ℕ) (i : Fin p) :
    (InitialNetwork.variableEquiv p n t (Sum.inl i)).val = i.val := rfl

/-- Exact bit-for-bit agreement, including clause order, signs, and all nested
literal/list delimiters, with the actual initial-network CNF. -/
theorem bits_eq_sourceClauses (t : ℕ) (v : Fin n) (s : InputSource p) :
    bits (p+v.val) s = (InitialNetwork.sourceClauses t v s).flatMap
      (fun c => serializedClause (c.map (fun l => ((InitialNetwork.variableEquiv p n t l.1).val,l.2)))) := by
  cases s with
  | constant value => simp [bits,InitialNetwork.sourceClauses,initial_target_val]
  | bit i negate =>
    simp only [bits,bitBits,InitialNetwork.sourceClauses,TruthTableCNF.clauses,patterns,
      List.flatMap_assoc]
    apply List.flatMap_congr
    intro a ha
    simp [TruthTableCNF.constraint,TruthTableCNF.mismatch,List.ofFn_succ,
      rawBitClause,initial_target_val,input_val]

/-- Operational endpoint phrased directly in terms of the paper's initial
source clauses and the proved dense variable equivalence. -/
theorem sourceClauses_executes (g : BitString → ℕ) (t : ℕ) (v : Fin n)
    (s : InputSource p) (stream : BitString) :
    (program s).Executes g (state (sourceIndex s) (p+v.val) 0 0 stream)
      (state (sourceIndex s) (p+v.val) 0 0
        (((InitialNetwork.sourceClauses t v s).flatMap (fun c => serializedClause
          (c.map (fun l => ((InitialNetwork.variableEquiv p n t l.1).val,l.2))))).reverse++stream))
      (cost (p+v.val) s) := by
  rw [←bits_eq_sourceClauses]
  exact program_executes g s _ stream

noncomputable def programOn (φ : Fin 5 ↪ Fin (k+1)) (s : InputSource p) : OracleBlock k :=
  rename (program s) φ

/-- The emitter can be placed in any five distinct stacks. Every stack outside
its output is restored, including arbitrary surrounding machine metadata. -/
theorem programOn_executes (φ : Fin 5 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : InputSource p) (target : ℕ) (outer : Store k)
    (houter : outer ∘ φ = state (sourceIndex s) target 0 0 (outer (φ 4))) :
    (programOn φ s).Executes g outer
      (Function.update outer (φ 4) ((bits target s).reverse++outer (φ 4))) (cost target s) := by
  apply rename_executes_to _ φ g (program_executes g s target (outer (φ 4))) houter
  · funext i
    by_cases hi : i=4
    · subst i
      simp [Function.comp_def,state]
    · have hφ : φ i ≠ φ 4 := fun h => hi (φ.injective h)
      simp only [Function.comp_def,Function.update_of_ne hφ]
      have h := congrFun houter i
      simpa only [Function.comp_def] using h.trans (by
        fin_cases i <;> simp_all [state])
  · intro i hi
    exact Function.update_of_ne (fun h => hi 4 h.symm) _ _

lemma programOn_queryFree (φ : Fin 5 ↪ Fin (k+1)) (s : InputSource p) :
    (programOn φ s).QueryFree := rename_queryFree _ _ (program_queryFree s)

end HiddenCircuits.Complexity.InitialCellEmitter
