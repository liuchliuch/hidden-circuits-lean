import HiddenCircuits.Complexity.CNFCloneEmitter.UnarySplit
import HiddenCircuits.Complexity.CNFCloneEmitter.VertexSemantics
import HiddenCircuits.Complexity.UnaryDivision

/-! Actual unary clone-vertex classification, using real truncated subtraction
and quotient/remainder blocks. No index or arithmetic primitive is assumed. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter.VertexRuntime
open OracleBlock

/-- Masters0..3: index/cut/a/b. Result4..6: variable flag/group/sign.
Work7..12: dividend/quotient/remainder/division clock/copy work/two. -/
def store (x cut a b : ℕ) (tag : BitString) (number : ℕ) (sign : BitString)
    (dividend quotient remainder : ℕ) (temporary work : BitString) (two : ℕ) : Store 12 := fun i =>
  if i.val=0 then List.replicate x true else if i.val=1 then List.replicate cut true else
  if i.val=2 then List.replicate a true else if i.val=3 then List.replicate b true else
  if i.val=4 then tag else if i.val=5 then List.replicate number true else if i.val=6 then sign else
  if i.val=7 then List.replicate dividend true else if i.val=8 then List.replicate quotient true else
  if i.val=9 then List.replicate remainder true else if i.val=10 then temporary else if i.val=11 then work else List.replicate two true

def splitEmbedding : Fin 3 ↪ Fin 13 where
  toFun i := if i.val=0 then 7 else if i.val=1 then 8 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def divAEmbedding : Fin 6 ↪ Fin 13 where
  toFun i := if i.val=0 then 7 else if i.val=1 then 2 else if i.val=2 then 8 else if i.val=3 then 9 else if i.val=4 then 10 else 11
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def divBEmbedding : Fin 6 ↪ Fin 13 where
  toFun i := if i.val=0 then 7 else if i.val=1 then 3 else if i.val=2 then 5 else if i.val=3 then 9 else if i.val=4 then 10 else 11
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def halfEmbedding : Fin 6 ↪ Fin 13 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 12 else if i.val=2 then 5 else if i.val=3 then 9 else if i.val=4 then 10 else 11
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def split : OracleBlock 12 := rename UnarySplit.program splitEmbedding
noncomputable def divA : OracleBlock 12 := rename UnaryDivision.block divAEmbedding
noncomputable def divB : OracleBlock 12 := rename UnaryDivision.block divBEmbedding
noncomputable def half : OracleBlock 12 := rename UnaryDivision.block halfEmbedding
noncomputable def emitSign : OracleBlock 12 := branchPop 9 (push 6 false) (push 6 true) (push 6 true)

noncomputable def variableBranch : OracleBlock 12 :=
  seq (copyOn 0 7 11 (by decide) (by decide) (by decide))
    (seq divA (seq (clear 9) (seq (prepend 12 [true,true])
      (seq half (seq (clear 12) (seq emitSign (push 4 true)))))))
noncomputable def clauseBranch : OracleBlock 12 := seq divB (seq (clear 9) (seq (push 6 false) (push 4 false)))
noncomputable def classify : OracleBlock 12 := branchPop 4 skip clauseBranch variableBranch
noncomputable def program : OracleBlock 12 :=
  seq (copyOn 0 7 11 (by decide) (by decide) (by decide))
    (seq (copyOn 1 8 11 (by decide) (by decide) (by decide)) (seq split classify))

theorem divA_executes (g : BitString → ℕ) (x cut a b y : ℕ) (ha : 0<a) :
    ∃ cost, divA.Executes g (store x cut a b [] 0 [] y 0 0 [] [] 0)
      (store x cut a b [] 0 [] 0 (y/a) (y%a) [] [] 0) cost ∧ cost≤y*(6*a+18)+6*a+8 := by
  obtain ⟨c,hc,hb⟩ := UnaryDivision.block_executes g y a ha
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ divAEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim

theorem divB_executes (g : BitString → ℕ) (x cut a b y : ℕ) (hb : 0<b) :
    ∃ cost, divB.Executes g (store x cut a b [] 0 [] y 0 0 [] [] 0)
      (store x cut a b [] (y/b) [] 0 0 (y%b) [] [] 0) cost ∧ cost≤y*(6*b+18)+6*b+8 := by
  obtain ⟨c,hc,hb⟩ := UnaryDivision.block_executes g y b hb
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ divBEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim

theorem half_executes (g : BitString → ℕ) (x cut a b q : ℕ) :
    ∃ cost, half.Executes g (store x cut a b [] 0 [] 0 q 0 [] [] 2)
      (store x cut a b [] (q/2) [] 0 0 (q%2) [] [] 2) cost ∧ cost≤30*q+20 := by
  obtain ⟨c,hc,hb⟩ := UnaryDivision.block_executes g q 2 (by decide)
  refine ⟨c,?_,by omega⟩
  apply rename_executes_to _ halfEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim

theorem emitSign_executes (g : BitString → ℕ) (x cut a b q r : ℕ) (hr : r<2) :
    emitSign.Executes g (store x cut a b [] q [] 0 0 r [] [] 0)
      (store x cut a b [] q [decide (r=1)] 0 0 0 [] [] 0) 3 := by
  have hcases : r=0 ∨ r=1 := by omega
  rcases hcases with rfl | rfl
  · apply branchPop_empty _ _ _ _ g rfl
    have he : Function.update (store x cut a b [] q [] 0 0 0 [] [] 0) (9:Fin 13) []=
        store x cut a b [] q [] 0 0 0 [] [] 0 := by funext i;fin_cases i <;> rfl
    try simp only [List.replicate_zero,he]
    convert push_executes g (6 : Fin 13) false (store x cut a b [] q [] 0 0 0 [] [] 0) using 1
    funext i;fin_cases i <;> rfl
  · apply branchPop_true _ _ _ _ g rfl
    have he : Function.update (store x cut a b [] q [] 0 0 1 [] [] 0) (9:Fin 13) []=
        store x cut a b [] q [] 0 0 0 [] [] 0 := by funext i;fin_cases i <;> rfl
    try simp only [List.replicate_zero,he]
    convert push_executes g (6 : Fin 13) true (store x cut a b [] q [] 0 0 0 [] [] 0) using 1
    funext i;fin_cases i <;> rfl

theorem variableBranch_executes (g : BitString → ℕ) (x cut a b : ℕ) (ha : 0<a) :
    ∃ cost, variableBranch.Executes g (store x cut a b [] 0 [] 0 0 0 [] [] 0)
      (store x cut a b [true] ((x/a)/2) [decide ((x/a)%2=1)] 0 0 0 [] [] 0) cost ∧
      cost≤100*(x+a+1)^2 := by
  have h1 : (copyOn (0:Fin 13) 7 11 (by decide) (by decide) (by decide)).Executes g
      (store x cut a b [] 0 [] 0 0 0 [] [] 0) (store x cut a b [] 0 [] x 0 0 [] [] 0) (5*x+2) := by
    convert copyOn_executes g (0:Fin 13) 7 11 (by decide) (by decide) (by decide)
      (store x cut a b [] 0 [] 0 0 0 [] [] 0) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨c2,h2,hb2⟩ := divA_executes g x cut a b x ha
  have h3 : (clear (9:Fin 13)).Executes g (store x cut a b [] 0 [] 0 (x/a) (x%a) [] [] 0)
      (store x cut a b [] 0 [] 0 (x/a) 0 [] [] 0) (x%a+1) := by
    convert clear_executes g (9:Fin 13) (store x cut a b [] 0 [] 0 (x/a) (x%a) [] [] 0) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h4 : (prepend (12:Fin 13) [true,true]).Executes g (store x cut a b [] 0 [] 0 (x/a) 0 [] [] 0)
      (store x cut a b [] 0 [] 0 (x/a) 0 [] [] 2) 7 := by
    convert prepend_executes g (12:Fin 13) [true,true] (store x cut a b [] 0 [] 0 (x/a) 0 [] [] 0) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c5,h5,hb5⟩ := half_executes g x cut a b (x/a)
  have h6 : (clear (12:Fin 13)).Executes g (store x cut a b [] ((x/a)/2) [] 0 0 ((x/a)%2) [] [] 2)
      (store x cut a b [] ((x/a)/2) [] 0 0 ((x/a)%2) [] [] 0) 3 := by
    convert clear_executes g (12:Fin 13) (store x cut a b [] ((x/a)/2) [] 0 0 ((x/a)%2) [] [] 2) using 1
    funext i;fin_cases i <;> rfl
  have h7 := emitSign_executes g x cut a b ((x/a)/2) ((x/a)%2) (Nat.mod_lt _ (by decide))
  have h8 : (push (4:Fin 13) true).Executes g
      (store x cut a b [] ((x/a)/2) [decide ((x/a)%2=1)] 0 0 0 [] [] 0)
      (store x cut a b [true] ((x/a)/2) [decide ((x/a)%2=1)] 0 0 0 [] [] 0) 1 := by
    convert push_executes g (4:Fin 13) true (store x cut a b [] ((x/a)/2) [decide ((x/a)%2=1)] 0 0 0 [] [] 0) using 1
    funext i;fin_cases i <;> rfl
  refine ⟨5*x+2+(c2+((x%a+1)+(7+(c5+(3+(3+1+2)+2)+2)+2)+2)+2)+2,
    seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4
      (seq_executes _ _ g h5 (seq_executes _ _ g h6 (seq_executes _ _ g h7 h8)))))),?_⟩
  have hq := Nat.div_le_self x a
  have hr := Nat.mod_lt x ha
  nlinarith

theorem clauseBranch_executes (g : BitString → ℕ) (x cut a b y : ℕ) (hb : 0<b) :
    ∃ cost, clauseBranch.Executes g (store x cut a b [] 0 [] y 0 0 [] [] 0)
      (store x cut a b [false] (y/b) [false] 0 0 0 [] [] 0) cost ∧ cost≤100*(y+b+1)^2 := by
  obtain ⟨c1,h1,hb1⟩ := divB_executes g x cut a b y hb
  have h2 : (clear (9:Fin 13)).Executes g (store x cut a b [] (y/b) [] 0 0 (y%b) [] [] 0)
      (store x cut a b [] (y/b) [] 0 0 0 [] [] 0) (y%b+1) := by
    convert clear_executes g (9:Fin 13) (store x cut a b [] (y/b) [] 0 0 (y%b) [] [] 0) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h3 : (push (6:Fin 13) false).Executes g (store x cut a b [] (y/b) [] 0 0 0 [] [] 0)
      (store x cut a b [] (y/b) [false] 0 0 0 [] [] 0) 1 := by
    convert push_executes g (6:Fin 13) false (store x cut a b [] (y/b) [] 0 0 0 [] [] 0) using 1
    funext i;fin_cases i <;> rfl
  have h4 : (push (4:Fin 13) false).Executes g (store x cut a b [] (y/b) [false] 0 0 0 [] [] 0)
      (store x cut a b [false] (y/b) [false] 0 0 0 [] [] 0) 1 := by
    convert push_executes g (4:Fin 13) false (store x cut a b [] (y/b) [false] 0 0 0 [] [] 0) using 1
    funext i;fin_cases i <;> rfl
  refine ⟨c1+((y%b+1)+(1+1+2)+2)+2,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  have hm := Nat.mod_lt y hb
  nlinarith

end HiddenCircuits.Complexity.CNFCloneEmitter.VertexRuntime
