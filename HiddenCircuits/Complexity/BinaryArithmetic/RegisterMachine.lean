import HiddenCircuits.Complexity.BinaryArithmetic.Operations

/-! Compile ordinary straight-line integer assignments into finite bit programs.
Every register is a canonical signed bit string; copies, arithmetic, overwritten
outputs and work cleanup are all counted instructions. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
open OracleBlock Polynomial

def dataPort (i : Fin 7) : Fin 16 := ⟨9+i.val,by omega⟩
def workPort : Fin 9 ↪ Fin 16 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun t : Fin 16 => t.val) h)

def store (a b : BitString) (R : Fin 7 → BitString) : Store 15 := fun (i : Fin 16) =>
  if i.val=0 then a else if i.val=1 then b else
  if h : 9 ≤ i.val then R ⟨i.val - 9, by omega⟩ else []

@[simp] lemma store_zero (a b : BitString) (R : Fin 7 → BitString) : store a b R 0=a := rfl
@[simp] lemma store_one (a b : BitString) (R : Fin 7 → BitString) : store a b R 1=b := rfl
@[simp] lemma store_data (a b : BitString) (R : Fin 7 → BitString) (i : Fin 7) :
    store a b R (dataPort i)=R i := by fin_cases i <;> rfl
@[simp] lemma store_work (a b : BitString) (R : Fin 7 → BitString) (i : Fin 9) :
    store a b R (workPort i)=binaryStore a b i := by
  fin_cases i <;> simp [store,workPort,binaryStore]

lemma update_zero (a b z : BitString) (R : Fin 7 → BitString) :
    Function.update (store a b R) (0 : Fin 16) z=store z b R := by
  funext i;fin_cases i <;> rfl
lemma update_one (a b z : BitString) (R : Fin 7 → BitString) :
    Function.update (store a b R) (1 : Fin 16) z=store a z R := by
  funext i;fin_cases i <;> rfl
lemma update_data (a b z : BitString) (R : Fin 7 → BitString) (d : Fin 7) :
    Function.update (store a b R) (dataPort d) z=store a b (Function.update R d z) := by
  fin_cases d <;> funext i <;> fin_cases i <;> rfl

noncomputable def readLeft (i : Fin 7) : OracleBlock 15 :=
  copyOn (dataPort i) 0 2 (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by decide)
noncomputable def readRight (i : Fin 7) : OracleBlock 15 :=
  copyOn (dataPort i) 1 2 (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by decide)
noncomputable def executeOp (op : Operation) : OracleBlock 15 := rename op.program workPort
noncomputable def writeResult (d : Fin 7) : OracleBlock 15 :=
  seq (clear (dataPort d)) (moveOn 0 (dataPort d) 2
    (by fin_cases d <;> decide) (by decide) (by fin_cases d <;> decide))

lemma readLeft_executes (g : BitString → ℕ) (i : Fin 7) (R : Fin 7 → BitString) :
    (readLeft i).Executes g (store [] [] R) (store (R i) [] R) (5*(R i).length+2) := by
  simpa only [store_data,store_zero,List.append_nil,update_zero] using
    copyOn_executes g (dataPort i) (0 : Fin 16) 2 _ _ _ (store [] [] R) rfl
lemma readRight_executes (g : BitString → ℕ) (i : Fin 7) (a : BitString) (R : Fin 7 → BitString) :
    (readRight i).Executes g (store a [] R) (store a (R i) R) (5*(R i).length+2) := by
  simpa only [store_data,store_one,List.append_nil,update_one] using
    copyOn_executes g (dataPort i) (1 : Fin 16) 2 _ _ _ (store a [] R) rfl

lemma executeOp_executes (g : BitString → ℕ) (op : Operation) (a b : ℤ)
    (hv : op.Valid a b) (R : Fin 7 → BitString) :
    ∃ t, (executeOp op).Executes g (store (signedBits a) (signedBits b) R)
      (store (signedBits (op.eval a b)) [] R) t ∧
      t ≤ operationTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨t,ht,hb⟩ := op.executes g a b hv
  refine ⟨t,?_,hb⟩
  apply rename_executes_to op.program workPort g ht
  · funext i;exact store_work _ _ _ i
  · funext i;exact store_work _ _ _ i
  · intro j hj
    have hj9 : 9≤j.val := by
      by_contra hn
      exact hj ⟨j.val,by omega⟩ (Fin.ext rfl)
    simp [store,show j.val≠0 by omega,show j.val≠1 by omega]

lemma writeResult_executes (g : BitString → ℕ) (d : Fin 7) (z : BitString) (R : Fin 7 → BitString) :
    (writeResult d).Executes g (store z [] R) (store [] [] (Function.update R d z))
      ((R d).length+6*z.length+8) := by
  have hc : (clear (dataPort d)).Executes g (store z [] R) (store z [] (Function.update R d []))
      ((R d).length+1) := by
    simpa only [store_data,update_data] using clear_executes g (dataPort d) (store z [] R)
  have hm := moveOn_executes g (0 : Fin 16) (dataPort d) 2
    (by fin_cases d <;> decide) (by decide) (by fin_cases d <;> decide)
    (store z [] (Function.update R d [])) rfl
  simp only [store_zero,store_data,Function.update_self,List.append_nil,update_data,
    Function.update_idem,update_zero] at hm
  convert seq_executes _ _ g hc hm using 1 <;> omega

noncomputable def assign (op : Operation) (d i j : Fin 7) : OracleBlock 15 :=
  seq (readLeft i) (seq (readRight j) (seq (executeOp op) (writeResult d)))

/-- Exact semantic assignment, including reading both old source operands before
possibly overwriting one of them. -/
theorem assign_executes (g : BitString → ℕ) (op : Operation) (d i j : Fin 7) (R : Fin 7 → ℤ)
    (hv : op.Valid (R i) (R j)) :
    ∃ t, (assign op d i j).Executes g (store [] [] (signedBits ∘ R))
      (store [] [] (signedBits ∘ Function.update R d (op.eval (R i) (R j)))) t ∧
      t ≤ 5*(signedBits (R i)).length+5*(signedBits (R j)).length+
        operationTime.eval ((signedBits (R i)).length+(signedBits (R j)).length)+
        (signedBits (R d)).length+6*(signedBits (op.eval (R i) (R j))).length+18 := by
  obtain ⟨c,hc,hb⟩ := executeOp_executes g op (R i) (R j) hv (signedBits ∘ R)
  have h := seq_executes _ _ g (readLeft_executes g i (signedBits ∘ R))
    (seq_executes _ _ g (readRight_executes g j (signedBits (R i)) (signedBits ∘ R))
      (seq_executes _ _ g hc (writeResult_executes g d (signedBits (op.eval (R i) (R j))) (signedBits ∘ R))))
  refine ⟨5*(signedBits (R i)).length+5*(signedBits (R j)).length+c+
    (signedBits (R d)).length+6*(signedBits (op.eval (R i) (R j))).length+18,?_,?_⟩
  · convert h using 1
    · congr 1
      funext q
      by_cases hq : q=d
      · subst q;simp [Function.comp_def]
      · simp [Function.comp_def,hq]
    · dsimp [Function.comp_def];omega
  · dsimp [Function.comp_def] at *;omega

lemma assign_queryFree (op : Operation) (d i j : Fin 7) : (assign op d i j).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _
    (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ op.queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _))))

end HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
