import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine
import HiddenCircuits.Complexity.BinaryArithmetic.SignFlag
import HiddenCircuits.GraphReduction.Runtime.SeedFlags
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! Fixed six-assignment signed binary comparison of two endpoints at distance d. -/
namespace HiddenCircuits.GraphReduction.Runtime.IntegerDistance
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

def init (d x y : ℤ) : Fin 7 → ℤ := ![d,x,y,-1,0,0,0]
def code : List Instruction := [⟨.multiply,4,1,3⟩,⟨.multiply,5,2,3⟩,
  ⟨.add,4,4,2⟩,⟨.add,5,5,1⟩,⟨.add,4,4,0⟩,⟨.add,5,5,0⟩]
lemma code_value (d x y : ℤ) : evaluate code (init d x y)=![d,x,y,-1,d-x+y,d-y+x,0] := by
  funext i;fin_cases i <;> simp [code,evaluate,Instruction.eval,Operation.eval,init] <;> ring
lemma code_valid (d x y : ℤ) : Valid code (init d x y) := by simp [code,Valid,Operation.Valid]

def arithMap : Fin 16 ↪ Fin 17 where
  toFun i := if h:i.val<9 then ⟨i.val+8,by omega⟩ else
    if i.val=9 then 0 else if i.val=10 then 1 else if i.val=11 then 2 else ⟨i.val-8,by omega⟩
  inj' := by decide +kernel

def state (d x y result r3 r4 r5 r6 : BitString) : Store 16 := fun i=>
  if i.val=0 then d else if i.val=1 then x else if i.val=2 then y else if i.val=3 then result
  else if i.val=4 then r3 else if i.val=5 then r4 else if i.val=6 then r5 else if i.val=7 then r6 else []
def arithState (R : Fin 7 → ℤ) : Store 16 := state (signedBits (R 0)) (signedBits (R 1)) (signedBits (R 2)) []
  (signedBits (R 3)) (signedBits (R 4)) (signedBits (R 5)) (signedBits (R 6))
def input (d x y : ℤ) : Store 16 := state (signedBits d) (signedBits x) (signedBits y) [] [] [] [] []
def answer (d x y : ℤ) : Bool := decide (x-y≤d ∧y-x≤d)

noncomputable def seed : OracleBlock 16 := seedFlags [(4,true),(4,true),(5,false),(6,false),(7,false)]
noncomputable def compute : OracleBlock 16 := rename (compile code) arithMap
noncomputable def decideSigns : OracleBlock 16 := Complexity.GraphVerifier.Runtime.decision 3 [8,9]
  (fun bs=> !(bs[0]?.getD true ||bs[1]?.getD true))
noncomputable def finish : OracleBlock 16 := seq (SignFlag.on 5 8 (by decide))
  (seq (SignFlag.on 6 9 (by decide)) (seq decideSigns (clearList [0,1,2,4,7])))
noncomputable def program : OracleBlock 16 := seq seed (seq compute finish)
noncomputable def resultBound (B : ℕ) := 64*(B+3)
noncomputable def time : Polynomial ℕ := straightTime code + 10*(64*(Polynomial.X+3))+100

lemma init_bounded (d x y : ℤ) (B : ℕ) (hd:(signedBits d).length≤B) (hx:(signedBits x).length≤B)
    (hy:(signedBits y).length≤B) (hB:2≤B) : Bounded B (init d x y) := by
  intro i;fin_cases i
  · exact hd
  · exact hx
  · exact hy
  · norm_num [init,signedBits,negative,Computability.encodeNat,Computability.encodeNum,Computability.encodePosNum]
    exact hB
  all_goals change 1≤B;omega
lemma result_bounded (d x y : ℤ) (B : ℕ) (hb:Bounded B (init d x y)) :
    Bounded (resultBound B) (evaluate code (init d x y)) :=
  (safe_of_bounded code (init d x y) B hb (code_valid d x y)).final
end HiddenCircuits.GraphReduction.Runtime.IntegerDistance
