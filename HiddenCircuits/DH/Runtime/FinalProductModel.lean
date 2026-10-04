import HiddenCircuits.DH.Runtime.NumericEncoding
import HiddenCircuits.Circuit.Runtime.SamplePairParser
import HiddenCircuits.Complexity.BinaryArithmetic.Operations
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorBounds

/-! Fresh reconstruction: live-root coefficient product and its physical14-port layout. -/
namespace HiddenCircuits.DH.Runtime.FinalProduct
open Complexity OracleBlock BinaryArithmetic
abbrev Rows := List (Bool×List ℕ)
def live (xs : Rows) : BitString := encodeBitList (xs.map (fun x => [x.1]))
def table (xs : Rows) : BitString := encodeBitList (xs.map (fun x => NumericEncoding.rowBits x.2))
def factor (x : Bool×List ℕ) : ℕ := if x.1 then CoefficientModel.read x.2 0 else 1
def product (xs : Rows) : ℕ := (xs.map factor).prod
def factors (xs : Rows) : List ℤ := xs.map (fun (x : Bool×List ℕ) => (factor x:ℤ))
def store (alive rows row mark acc item : BitString) : Store 13 := fun i =>
  if i.val=0 then alive else if i.val=1 then rows else if i.val=2 then row
  else if i.val=3 then mark else if i.val=4 then acc else if i.val=5 then item else []
def loopStore (xs : Rows) (a : ℕ) : Store 13 := store (live xs) (table xs) [] [] (signedBits (a:ℤ)) []
def initial (alive rows : BitString) : Store 13 := store alive rows [] [] [] []

lemma product_cons (b : Bool) (row : List ℕ) (xs : Rows) :
    product ((b,row)::xs)=(if b then CoefficientModel.read row 0 else 1)*product xs := rfl
@[simp] lemma live_cons (b : Bool) (row : List ℕ) (xs : Rows) :
    live ((b,row)::xs)=true::pairBits [b] (live xs) := rfl
@[simp] lemma table_cons (b : Bool) (row : List ℕ) (xs : Rows) :
    table ((b,row)::xs)=true::pairBits (NumericEncoding.rowBits row) (table xs) := rfl
lemma rowBits_cons (x : ℕ) (xs : List ℕ) : NumericEncoding.rowBits (x::xs)=
    true::pairBits (signedBits (x:ℤ)) (NumericEncoding.rowBits xs) := rfl

noncomputable def bodyBound (B R : ℕ) : ℕ := operationTime.eval (B+R)+12*R+50

def liveMap : Fin 4 ↪ Fin 14 where
  toFun i := ![0,3,6,7] i
  inj' := by decide +kernel
def rowMap : Fin 4 ↪ Fin 14 where
  toFun i := ![1,2,6,7] i
  inj' := by decide +kernel
def headMap : Fin 4 ↪ Fin 14 where
  toFun i := ![2,5,6,7] i
  inj' := by decide +kernel
def mulMap : Fin 9 ↪ Fin 14 where
  toFun i := ![4,5,6,7,8,9,10,11,12] i
  inj' := by decide +kernel
noncomputable def parseLive : OracleBlock 13 := Circuit.Runtime.SamplePairParser.on liveMap
noncomputable def parseRow : OracleBlock 13 := branchPop 1 skip
  (Circuit.Runtime.SamplePairParser.on rowMap) (Circuit.Runtime.SamplePairParser.on rowMap)
noncomputable def parseHead : OracleBlock 13 := branchPop 2 skip
  (Circuit.Runtime.SamplePairParser.on headMap) (Circuit.Runtime.SamplePairParser.on headMap)
noncomputable def multiply : OracleBlock 13 := rename Operation.multiply.program mulMap
noncomputable def choose : OracleBlock 13 := branchPop 3 skip (clear 5) multiply
noncomputable def body : OracleBlock 13 := seq parseLive (seq parseRow (seq parseHead (seq (clear 2) choose)))
noncomputable def loop : OracleBlock 13 := whilePop 0 body body
end HiddenCircuits.DH.Runtime.FinalProduct
