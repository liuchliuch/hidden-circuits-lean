import HiddenCircuits.DH.ModuleMerge
import HiddenCircuits.DH.LexBFSPartition

/-! Direct-array implementation of labeled-cotree bag substitution and module deletion.
The expression table keeps old bags at leaves; only new cotree merge nodes are allocated. -/
namespace HiddenCircuits.DH.ModuleExecution
open LexBFSPartition

structure SubstitutionResult where
  expression : BagExpr
  accesses : ℕ
  allocated : ℕ

def substituteArray {n : ℕ} (bags : Vector BagExpr n) : LabeledCographTree (Fin n) → SubstitutionResult
  | .leaf v => ⟨bags[v.val],2,0⟩
  | .node false l r =>
      let a := substituteArray bags l
      let b := substituteArray bags r
      ⟨.falseTwin a.expression b.expression,a.accesses+b.accesses+2,a.allocated+b.allocated+1⟩
  | .node true l r =>
      let a := substituteArray bags l
      let b := substituteArray bags r
      ⟨.trueTwin a.expression b.expression,a.accesses+b.accesses+2,a.allocated+b.allocated+1⟩

@[simp] theorem substituteArray_expression {n : ℕ} (bags : Vector BagExpr n) (t : LabeledCographTree (Fin n)) :
    (substituteArray bags t).expression = t.substitute (fun v => bags[v.val]) := by
  induction t with
  | leaf v => rfl
  | node b l r hl hr => cases b <;> simp [substituteArray,LabeledCographTree.substitute,hl,hr]

/-- Each actual old-bag lookup and each new cotree node is charged explicitly. -/
theorem substituteArray_resources {n : ℕ} (bags : Vector BagExpr n) (t : LabeledCographTree (Fin n)) :
    (substituteArray bags t).accesses = 2*t.shape.nodes ∧
      (substituteArray bags t).allocated+1 = t.shape.leaves := by
  induction t with
  | leaf v => exact ⟨rfl,rfl⟩
  | node b l r hl hr =>
    cases b <;> simp only [substituteArray,LabeledCographTree.shape,CographTree.nodes,CographTree.leaves]
    all_goals constructor <;> omega

/-- Delete the original representatives other than the selected survivor. -/
def markExcept {n : ℕ} (keep : Fin n) : List (Fin n) → Vector Bool n → Counted (Vector Bool n)
  | [],alive => ⟨alive,0⟩
  | v::vs,alive =>
      if v=keep then
        let q := markExcept keep vs alive
        ⟨q.value,q.accesses+1⟩
      else
        let q := markExcept keep vs (alive.set v.val false)
        ⟨q.value,q.accesses+3⟩

lemma markExcept_get {n : ℕ} (keep : Fin n) (vs : List (Fin n)) (alive : Vector Bool n) (v : Fin n) :
    (markExcept keep vs alive).value[v.val] =
      if v∈vs ∧ v≠keep then false else alive[v.val] := by
  induction vs generalizing alive with
  | nil => simp [markExcept]
  | cons x xs ih =>
    by_cases hx : x=keep
    · subst x
      simp only [markExcept,↓reduceIte,ih,List.mem_cons]
      by_cases hv : v=keep <;> simp [hv]
    · simp only [markExcept,hx,↓reduceIte,ih,List.mem_cons]
      by_cases hv : v=x
      · subst x; simp [hx]
      · have hxv : x.val≠v.val := fun he => hv (Fin.ext he).symm
        simp [hv,hxv]

lemma markExcept_accesses {n : ℕ} (keep : Fin n) (vs : List (Fin n)) (alive : Vector Bool n) :
    (markExcept keep vs alive).accesses ≤ 3*vs.length := by
  induction vs generalizing alive with
  | nil => simp [markExcept]
  | cons x xs ih =>
    by_cases hx : x=keep
    · have h := ih alive; simp only [markExcept,hx,↓reduceIte,List.length_cons]; omega
    · have h := ih (alive.set x.val false); simp only [markExcept,hx,↓reduceIte,List.length_cons]; omega

structure Store (n : ℕ) where
  alive : Vector Bool n
  bags : Vector BagExpr n

/-- Only the selected representative's bag slot changes; deletion touches just the block list. -/
def contract {n : ℕ} (s : Store n) (vertices : List (Fin n)) (keep : Fin n)
    (tree : LabeledCographTree (Fin n)) : Counted (Store n) :=
  let e := substituteArray s.bags tree
  let marks := markExcept keep vertices s.alive
  ⟨⟨marks.value,s.bags.set keep.val e.expression⟩,e.accesses+marks.accesses+1⟩

/-- The program implements literal live-set restriction to the module survivor. -/
theorem contract_alive {n : ℕ} (s : Store n) (vertices : List (Fin n)) (keep : Fin n)
    (tree : LabeledCographTree (Fin n)) (v : Fin n) :
    (contract s vertices keep tree).value.alive[v.val] = true ↔
      s.alive[v.val]=true ∧ (v=keep ∨ v∉vertices) := by
  simp only [contract,markExcept_get]
  by_cases hv : v∈vertices <;> by_cases hk : v=keep <;> simp [hv,hk]

@[simp] theorem contract_kept_bag {n : ℕ} (s : Store n) (vertices : List (Fin n)) (keep : Fin n)
    (tree : LabeledCographTree (Fin n)) :
    (contract s vertices keep tree).value.bags[keep.val] = tree.substitute (fun v => s.bags[v.val]) := by
  simp [contract]

lemma contract_other_bag {n : ℕ} (s : Store n) (vertices : List (Fin n)) (keep : Fin n)
    (tree : LabeledCographTree (Fin n)) (v : Fin n) (hv : v≠keep) :
    (contract s vertices keep tree).value.bags[v.val] = s.bags[v.val] := by
  have hkv : keep.val≠v.val := fun he => hv (Fin.ext he).symm
  simp [contract,hkv]

theorem contract_accesses {n : ℕ} (s : Store n) (vertices : List (Fin n)) (keep : Fin n)
    (tree : LabeledCographTree (Fin n)) :
    (contract s vertices keep tree).accesses ≤ 2*tree.shape.nodes+3*vertices.length+1 := by
  have he := (substituteArray_resources s.bags tree).1
  have hm := markExcept_accesses keep vertices s.alive
  change (substituteArray s.bags tree).accesses+(markExcept keep vertices s.alive).accesses+1 ≤ _
  omega

end HiddenCircuits.DH.ModuleExecution
