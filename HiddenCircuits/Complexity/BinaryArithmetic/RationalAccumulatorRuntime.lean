import HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator
import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine

/-! The online rational accumulator is an
actual sixteen-stack binary program. Three integer multiplications and one
addition are compiled, and all temporary and consumed item bytes are cleared. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator
open OracleBlock Polynomial
set_option maxHeartbeats 1000000

def input (a b : Ratio) : Store 15 := fun i =>
  if i.val=9 then signedBits a.1 else if i.val=10 then signedBits a.2
  else if i.val=11 then signedBits b.1 else if i.val=12 then signedBits b.2 else []
def output (a : Ratio) : Store 15 := fun i =>
  if i.val=9 then signedBits a.1 else if i.val=10 then signedBits a.2 else []
def registers (a b : Ratio) : Fin 7 → ℤ := ![a.1,a.2,b.1,b.2,0,0,0]
def code : List RegisterMachine.Instruction :=
  [⟨.multiply,4,0,3⟩,⟨.multiply,5,2,1⟩,⟨.multiply,6,1,3⟩,⟨.add,0,4,5⟩]
def resultRegisters (a b : Ratio) : Fin 7 → ℤ :=
  ![a.1*b.2+b.1*a.2,a.2,b.1,b.2,a.1*b.2,b.1*a.2,a.2*b.2]

lemma code_evaluate (a b : Ratio) : RegisterMachine.evaluate code (registers a b)=resultRegisters a b := by
  funext i
  fin_cases i <;> simp [code,RegisterMachine.evaluate,RegisterMachine.Instruction.eval,Operation.eval,registers,resultRegisters]
lemma code_valid (a b : Ratio) : RegisterMachine.Valid code (registers a b) := by
  simp [code,RegisterMachine.Valid,Operation.Valid]
lemma registers_bounded (a b : Ratio) (B : ℕ) (ha : Bounded B a) (hb : Bounded B b) :
    RegisterMachine.Bounded (B+1) (registers a b) := by
  intro i
  fin_cases i <;> dsimp only [registers]
  all_goals first | exact ha.1.trans (by omega) | exact ha.2.trans (by omega) |
    exact hb.1.trans (by omega) | exact hb.2.trans (by omega) | (change 1≤B+1;omega)

noncomputable def seed : OracleBlock 15 := seq (push 13 false) (seq (push 14 false) (push 15 false))
noncomputable def finish : OracleBlock 15 :=
  seq (clearList [10,11,12,13,14]) (moveOn 15 10 2 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 15 := seq seed (seq (RegisterMachine.compile code) finish)
noncomputable def time : Polynomial ℕ := 12*(RegisterMachine.straightTime code).comp (X+1)+11*X+60

lemma seed_executes (g : BitString → ℕ) (a b : Ratio) :
    seed.Executes g (input a b) (RegisterMachine.store [] [] (signedBits ∘ registers a b)) 7 := by
  let s1 := Function.update (input a b) (13:Fin 16) [false]
  let s2 := Function.update s1 (14:Fin 16) [false]
  have h1 : (push (13:Fin 16) false).Executes g (input a b) s1 1 := push_executes g _ _ _
  have h2 : (push (14:Fin 16) false).Executes g s1 s2 1 := push_executes g _ _ _
  have h3 : (push (15:Fin 16) false).Executes g s2
      (RegisterMachine.store [] [] (signedBits ∘ registers a b)) 1 := by
    convert push_executes g (15:Fin 16) false s2 using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)

lemma finish_executes (g : BitString → ℕ) (a b : Ratio) (N : ℕ)
    (hs : ∀i,(RegisterMachine.store [] [] (signedBits ∘ resultRegisters a b) i).length≤N) :
    ∃t,finish.Executes g (RegisterMachine.store [] [] (signedBits ∘ resultRegisters a b))
      (output (step a b)) t ∧ t≤11*N+23 := by
  let s := RegisterMachine.store [] [] (signedBits ∘ resultRegisters a b)
  let mid := eraseStore ([10,11,12,13,14]:List (Fin 16)) s
  obtain ⟨c,hc,hbc⟩ := clearList_executes g ([10,11,12,13,14]:List (Fin 16)) s N hs
  have hmove := moveOn_executes g (15:Fin 16) 10 2 (by decide) (by decide) (by decide) mid rfl
  have he : Function.update (Function.update mid (10:Fin 16) (mid 15++mid 10)) (15:Fin 16) []=
      output (step a b) := by
    funext i;fin_cases i <;> simp [mid,s,eraseStore,RegisterMachine.store,resultRegisters,output,step]
  rw [he] at hmove
  refine ⟨_,seq_executes _ _ g hc hmove,?_⟩
  have hd : (mid 15).length≤N := hs 15
  simp only [List.length_cons,List.length_nil] at hbc
  omega

/-- The only supplied bounds are input bit lengths. Intermediate arithmetic and
all clearing costs follow from the physical compiled computation. -/
theorem program_executes (g : BitString → ℕ) (a b : Ratio) (B : ℕ)
    (ha : Bounded B a) (hb : Bounded B b) :
    ∃t,program.Executes g (input a b) (output (step a b)) t ∧ t≤time.eval B := by
  obtain ⟨c,hc,hbc⟩ := RegisterMachine.compile_polynomial code g (registers a b) (B+1)
    (registers_bounded a b B ha hb) (code_valid a b)
  rw [code_evaluate] at hc
  have hinit : ∀i,(RegisterMachine.store [] [] (signedBits ∘ registers a b) i).length≤B+1 := by
    intro i
    fin_cases i <;> first | exact Nat.zero_le _ |
      exact registers_bounded a b B ha hb 0 | exact registers_bounded a b B ha hb 1 |
      exact registers_bounded a b B ha hb 2 | exact registers_bounded a b B ha hb 3 |
      exact registers_bounded a b B ha hb 4
  obtain ⟨d,hd,hbd⟩ := finish_executes g a b (B+1+c) (hc.stack_bound hinit)
  refine ⟨_,seq_executes _ _ g (seed_executes g a b) (seq_executes _ _ g hc hd),?_⟩
  simp only [time,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat,eval_one]
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)))
  (seq_queryFree _ _ (RegisterMachine.compile_queryFree code)
    (seq_queryFree _ _ (clearList_queryFree _) (moveOn_queryFree _ _ _ _ _ _)))

noncomputable def on {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) : OracleBlock k := rename program φ

/-- Reusable bank interface. Item numerator and denominator are consumed; the
accumulator is updated at ports 9/10, and every off-bank stack is preserved. -/
theorem on_executes {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (a b : Ratio) (B : ℕ) (hshape : s∘φ=input a b)
    (ha : Bounded B a) (hb : Bounded B b) :
    ∃t,(on φ).Executes g s (install φ s (output (step a b))) t ∧ t≤time.eval B := by
  obtain ⟨t,ht,hb⟩ := program_executes g a b B ha hb
  exact ⟨t,rename_executes program φ g s (by rw [hshape];exact ht),hb⟩
/-- A requested target store can be used directly, with a literal bank
projection and the usual off-image frame condition. -/
theorem on_executes_to {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s u : Store k) (a b : Ratio) (B : ℕ) (hshape : s∘φ=input a b)
    (hresult : u∘φ=output (step a b)) (hframe : ∀i,(∀j,φ j≠i) → u i=s i)
    (ha : Bounded B a) (hb : Bounded B b) :
    ∃t,(on φ).Executes g s u t ∧ t≤time.eval B := by
  obtain ⟨t,ht,hb⟩ := program_executes g a b B ha hb
  exact ⟨t,rename_executes_to program φ g ht hshape hresult hframe,hb⟩

lemma on_queryFree {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator
