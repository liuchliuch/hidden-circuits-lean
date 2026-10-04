import HiddenCircuits.Complexity.BinaryArithmetic.Addition
import HiddenCircuits.Complexity.BinaryArithmetic.MultiplicationBits
import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! Fixed finite-stack Horner multiplication, assembled from verified bit
blocks. No natural-number operation is executed as a unit-cost instruction. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

noncomputable def addBlock : OracleBlock 2 where
  labelCount := addMachine.labelCount
  start := addLabel (.readX false)
  exit := addLabel .halt
  code := addMachine.code
  exit_halt := by simp [addMachine,addCode]

def addStore (a b t : BitString) : Store 2 :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else t

def addCost (a b : BitString) : ℕ := addPhaseCost a b false+2*(addBits a b false).length+1

theorem addCost_le (a b : BitString) : addCost a b ≤ 5*max a.length b.length+6 := by
  have := addPhaseCost_le a b false
  have := length_addBits a b false
  unfold addCost
  omega

theorem addBlock_executes (g : BitString → ℕ) (a b : BitString) :
    addBlock.Executes g (addStore a b []) (addStore (addBits a b false) [] []) (addCost a b) :=
  add_steps g a b false

lemma addBlock_queryFree : addBlock.QueryFree := by
  intro q i o next
  change addCode (addLabel.symm q) ≠ .query i o next
  cases h : addLabel.symm q with
  | readX c => simp [addCode]
  | readY c a => cases a <;> simp [addCode]
  | emit a b c => simp [addCode]
  | finalCarry => simp [addCode]
  | reverse => simp [addCode]
  | reversePush b => simp [addCode]
  | halt => simp [addCode]

/-- The shift tests zero rather than creating a redundant leading zero. -/
abbrev doubleOn {k : ℕ} (stack : Fin (k+1)) : OracleBlock k where
  labelCount := 5
  start := 0
  exit := 4
  code q := if q = 0 then .pop stack 4 1 2
    else if q = 1 then .push stack false 3
    else if q = 2 then .push stack true 3
    else if q = 3 then .push stack false 4
    else .halt
  exit_halt := rfl

def doubleCost (a : BitString) : ℕ := if a = [] then 1 else 3

lemma doubleCost_le (a : BitString) : doubleCost a ≤ 3 := by
  unfold doubleCost; split <;> omega

theorem doubleOn_executes {k : ℕ} (g : BitString → ℕ) (stack : Fin (k+1)) (s : Store k) :
    (doubleOn stack).Executes g s (Function.update s stack (doubleBits (s stack))) (doubleCost (s stack)) := by
  cases hs : s stack with
  | nil =>
    have he : Function.update s stack [] = s := by rw [← hs]; exact Function.update_eq_self _ _
    simp only [hs,doubleBits,doubleCost,ite_true,he]
    exact Steps.single (by simp [OracleMachine.step,doubleOn,machine,config,hs])
  | cons b bs =>
    have hp : (doubleOn stack).machine.step g ((doubleOn stack).config 0 s) =
        some ((doubleOn stack).config (if b then 2 else 1) (Function.update s stack bs),1) := by
      cases b <;> simp [OracleMachine.step,doubleOn,machine,config,hs]
    have hq : (doubleOn stack).machine.step g
        ((doubleOn stack).config (if b then 2 else 1) (Function.update s stack bs)) =
        some ((doubleOn stack).config 3 s,1) := by
      have he : Function.update s stack (b::bs) = s := by rw [← hs]; exact Function.update_eq_self _ _
      cases b <;> simp [OracleMachine.step,doubleOn,machine,config,he]
    have hr : (doubleOn stack).machine.step g ((doubleOn stack).config 3 s) =
        some ((doubleOn stack).config 4 (Function.update s stack (false::b::bs)),1) := by
      simp [OracleMachine.step,doubleOn,machine,config,hs]
    simpa [hs,doubleBits,doubleCost] using (Steps.single hp).trans ((Steps.single hq).trans (Steps.single hr))

lemma doubleOn_queryFree {k : ℕ} (stack : Fin (k+1)) : (doubleOn stack).QueryFree := by
  intro q i o next
  fin_cases q <;> simp [machine,doubleOn]

/-- Multiplication uses six fixed bit stacks: scratch, multiplicand,
accumulator, copied addend, carry scratch, and unread multiplier bits. -/
def mulStore (scratch y acc dup tmp bits : BitString) : Store 5 := fun i =>
  if i.val = 0 then scratch else if i.val = 1 then y else if i.val = 2 then acc
  else if i.val = 3 then dup else if i.val = 4 then tmp else bits

def mulAddEmbedding : Fin 3 ↪ Fin 6 where
  toFun i := if i.val = 0 then 2 else if i.val = 1 then 3 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def mulAdd : OracleBlock 5 := rename addBlock mulAddEmbedding

/-- A renamed adder acts only on accumulator, copied addend, and carry scratch. -/
theorem mulAdd_executes (g : BitString → ℕ) (y acc rhs bits : BitString) :
    mulAdd.Executes g (mulStore [] y acc rhs [] bits)
      (mulStore [] y (addBits acc rhs false) [] [] bits) (addCost acc rhs) := by
  have h := rename_executes addBlock mulAddEmbedding g (mulStore [] y acc rhs [] bits)
    (by convert addBlock_executes g acc rhs using 1; funext i; fin_cases i <;> rfl)
  have he : install mulAddEmbedding (mulStore [] y acc rhs [] bits) (addStore (addBits acc rhs false) [] []) =
      mulStore [] y (addBits acc rhs false) [] [] bits := by
    funext i
    fin_cases i
    · exact install_off _ _ _ 0 (by intro j; fin_cases j <;> decide)
    · exact install_off _ _ _ 1 (by intro j; fin_cases j <;> decide)
    · exact install_image mulAddEmbedding _ _ 0
    · exact install_image mulAddEmbedding _ _ 1
    · exact install_image mulAddEmbedding _ _ 2
    · exact install_off _ _ _ 5 (by intro j; fin_cases j <;> decide)
  simpa only [he] using h

theorem mulDouble_executes (g : BitString → ℕ) (y acc bits : BitString) :
    (doubleOn (2 : Fin 6)).Executes g (mulStore [] y acc [] [] bits)
      (mulStore [] y (doubleBits acc) [] [] bits) (doubleCost acc) := by
  convert doubleOn_executes g (2 : Fin 6) (mulStore [] y acc [] [] bits) using 1
  funext i; fin_cases i <;> rfl

noncomputable def mulCopy : OracleBlock 5 := copyOn 1 3 0 (by decide) (by decide) (by decide)

theorem mulCopy_executes (g : BitString → ℕ) (y acc bits : BitString) :
    mulCopy.Executes g (mulStore [] y acc [] [] bits)
      (mulStore [] y acc y [] bits) (5*y.length+2) := by
  convert copyOn_executes g (1 : Fin 6) 3 0 (by decide) (by decide) (by decide)
    (mulStore [] y acc [] [] bits) rfl using 1
  funext i; fin_cases i <;> simp [mulStore]

noncomputable def mulBody (b : Bool) : OracleBlock 5 :=
  if b then seq (doubleOn 2) (seq mulCopy mulAdd) else doubleOn 2

def mulStepCost (y acc : BitString) (b : Bool) : ℕ :=
  if b then doubleCost acc+(5*y.length+2)+addCost (doubleBits acc) y+4 else doubleCost acc

theorem mulBody_executes (g : BitString → ℕ) (y acc bits : BitString) (b : Bool) :
    (mulBody b).Executes g (mulStore [] y acc [] [] bits)
      (mulStore [] y (mulStep y acc b) [] [] bits) (mulStepCost y acc b) := by
  cases b
  · exact mulDouble_executes g y acc bits
  · have h := seq_executes (doubleOn (2 : Fin 6)) (seq mulCopy mulAdd) g
      (mulDouble_executes g y acc bits)
      (seq_executes mulCopy mulAdd g (mulCopy_executes g y (doubleBits acc) bits)
        (mulAdd_executes g y (doubleBits acc) y bits))
    simpa [mulBody,mulStep,mulStepCost,Nat.add_assoc] using h

theorem mulStepCost_le (y acc : BitString) (b : Bool) :
    mulStepCost y acc b ≤ 5*acc.length+10*y.length+20 := by
  have h₁ := doubleCost_le acc
  have h₂ := addCost_le (doubleBits acc) y
  have h₃ := length_doubleBits acc
  cases b <;> simp only [mulStepCost,Bool.false_eq_true,ite_false,ite_true]
  · omega
  · omega

noncomputable def mulLoop : OracleBlock 5 := whilePop 5 (mulBody false) (mulBody true)

def mulLoopCost (y : BitString) : BitString → BitString → ℕ
  | [], _ => 1
  | b::bs, acc => 2+mulStepCost y acc b+mulLoopCost y bs (mulStep y acc b)

/-- Each Horner iteration includes the actual loop pop and return jump. -/
theorem mulLoop_executes (g : BitString → ℕ) (y bits acc : BitString) :
    mulLoop.Executes g (mulStore [] y acc [] [] bits)
      (mulStore [] y (mulFold y bits acc) [] [] []) (mulLoopCost y bits acc) := by
  apply whilePop_executes
  induction bits generalizing acc with
  | nil => exact WhileExecution.empty _ rfl
  | cons b bs ih =>
    have hs : Function.update (mulStore [] y acc [] [] (b::bs)) (5 : Fin 6) bs =
        mulStore [] y acc [] [] bs := by funext i; fin_cases i <;> rfl
    cases b
    · have h := WhileExecution.zero rfl
        (show (mulBody false).Executes g
          (Function.update (mulStore [] y acc [] [] (false::bs)) 5 bs)
          (mulStore [] y (mulStep y acc false) [] [] bs) (mulStepCost y acc false) by
          rw [hs]; exact mulBody_executes g y acc bs false)
        (ih (mulStep y acc false))
      convert h using 1 <;> simp only [mulFold,mulLoopCost] <;> omega
    · have h := WhileExecution.one rfl
        (show (mulBody true).Executes g
          (Function.update (mulStore [] y acc [] [] (true::bs)) 5 bs)
          (mulStore [] y (mulStep y acc true) [] [] bs) (mulStepCost y acc true) by
          rw [hs]; exact mulBody_executes g y acc bs true)
        (ih (mulStep y acc true))
      convert h using 1 <;> simp only [mulFold,mulLoopCost] <;> omega

/-- A polynomial bit-operation bound for the full input-dependent loop. -/
theorem mulLoopCost_le (y bits acc : BitString) :
    mulLoopCost y bits acc ≤
      1+bits.length*(5*(acc.length+bits.length*(y.length+2))+10*y.length+22) := by
  induction bits generalizing acc with
  | nil => simp [mulLoopCost]
  | cons b bs ih =>
    have hi := ih (mulStep y acc b)
    have hs := mulStepCost_le y acc b
    have hl := length_mulStep y acc b
    have hm := Nat.mul_le_mul_left (5*bs.length) hl
    simp only [mulLoopCost,List.length_cons]
    nlinarith

noncomputable def multiplicationBlock : OracleBlock 5 :=
  seq (reverseOn 0 5 (by decide)) mulLoop

/-- Both operands are actual binary words. The multiplicand is preserved and
all four work stacks are empty on exit. -/
theorem multiplicationBlock_executes (g : BitString → ℕ) (x y : BitString) :
    multiplicationBlock.Executes g (mulStore x y [] [] [] [])
      (mulStore [] y (mulBits x y) [] [] []) (2*x.length+mulLoopCost y x.reverse []+3) := by
  have hr : (reverseOn (0 : Fin 6) 5 (by decide)).Executes g (mulStore x y [] [] [] [])
      (mulStore [] y [] [] [] x.reverse) (2*x.length+1) := by
    convert reverseOn_executes g (0 : Fin 6) 5 (by decide) (mulStore x y [] [] [] []) using 1
    funext i; fin_cases i <;> simp [mulStore]
  have h := seq_executes (reverseOn (0 : Fin 6) 5 (by decide)) mulLoop g hr
    (mulLoop_executes g y x.reverse [])
  convert h using 1 <;> omega

/-- Multiplication is an actual fixed finite oracle-free program and its cost
is polynomial in the two input bit lengths. -/
theorem multiply_binary_output (g : BitString → ℕ) (m n : ℕ) :
    ∃ t : ℕ, multiplicationBlock.Executes g
      (mulStore (Computability.encodeNat m) (Computability.encodeNat n) [] [] [] [])
      (mulStore [] (Computability.encodeNat n) (Computability.encodeNat (m*n)) [] [] []) t ∧
      t ≤ 4+2*(Computability.encodeNat m).length+
        (Computability.encodeNat m).length*
          (5*((Computability.encodeNat m).length*((Computability.encodeNat n).length+2))+
            10*(Computability.encodeNat n).length+22) := by
  refine ⟨2*(Computability.encodeNat m).length+
    mulLoopCost (Computability.encodeNat n) (Computability.encodeNat m).reverse []+3,?_,?_⟩
  · simpa using multiplicationBlock_executes g (Computability.encodeNat m) (Computability.encodeNat n)
  · have h := mulLoopCost_le (Computability.encodeNat n) (Computability.encodeNat m).reverse []
    simp only [List.length_reverse,List.length_nil,Nat.zero_add] at h
    omega

lemma mulBody_queryFree (b : Bool) : (mulBody b).QueryFree := by
  have hc : mulCopy.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have ha : mulAdd.QueryFree := rename_queryFree _ _ addBlock_queryFree
  cases b
  · exact doubleOn_queryFree _
  · exact seq_queryFree _ _ (doubleOn_queryFree _) (seq_queryFree _ _ hc ha)

lemma multiplicationBlock_queryFree : multiplicationBlock.QueryFree :=
  seq_queryFree _ _ (reverseOn_queryFree _ _ _) (whilePop_queryFree _ _ _ (mulBody_queryFree false) (mulBody_queryFree true))

end HiddenCircuits.Complexity.BinaryArithmetic
