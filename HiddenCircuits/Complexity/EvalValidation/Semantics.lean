import HiddenCircuits.Complexity.EvalValidation.Field
import HiddenCircuits.Complexity.EvalValidation.Mask
import HiddenCircuits.Complexity.EvalValidation.WordAtom
import HiddenCircuits.Complexity.EvalEncodingSoundness

/-! Boolean semantics of the actual all-raw evaluation-input validator.
`pairMode=true` means PairEval; false means WordEval. -/
namespace HiddenCircuits.Complexity.EvalValidation.Semantics
open GraphVerifier

def atomValid (pairMode : Bool) (width atom : BitString) : Bool :=
  if pairMode then PairAtom.valid atom width else WordAtom.valid atom width

def validList (pairMode : Bool) (width : BitString) : BitString→Bool
  | [] => true
  | b::bs => let r:=parse bs
    (r.ok && b) && atomValid pairMode width r.left && validList pairMode width r.right
termination_by xs=>xs.length
decreasing_by exact Field.tail_shorter _ _

def runFlags (pairMode : Bool) (width : BitString) : BitString→BitString→BitString
  | [],flags => flags
  | b::bs,flags => let r:=parse bs
    runFlags pairMode width r.right (atomValid pairMode width r.left::(r.ok && b)::flags)
termination_by xs _=>xs.length
decreasing_by exact Field.tail_shorter _ _

lemma runFlags_all (pairMode : Bool) (width xs flags : BitString) :
    (runFlags pairMode width xs flags).all id= (validList pairMode width xs && flags.all id) := by
  induction xs using (measure List.length).wf.induction generalizing flags with
  | h xs ih =>
    cases xs with
    | nil => simp [runFlags,validList]
    | cons b bs =>
      rw [runFlags,ih (parse bs).right (Field.tail_shorter b bs),validList]
      simp [Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]

def header (xs : BitString) : BitString := (parse xs).left
def width (xs : BitString) : BitString := header xs++header xs
def first (xs : BitString) : ParseResult := Field.item (parse xs).right
def second (xs : BitString) : ParseResult := Field.item (first xs).right
def headerFlags (xs : BitString) : BitString :=
  [Field.marker (header xs),(header xs).all id,(parse xs).ok]
def parsedFlags (xs : BitString) : BitString :=
  Mask.valid (second xs).left (header xs) (width xs)::Field.valid (first xs).right::
    Mask.valid (first xs).left (header xs) (width xs)::Field.valid (parse xs).right::headerFlags xs
def nonemptyFlag (pairMode : Bool) (xs : BitString) : Bool := if pairMode then !xs.isEmpty else true
def beforeFlags (pairMode : Bool) (xs : BitString) : BitString := nonemptyFlag pairMode (second xs).right::parsedFlags xs
def test (pairMode : Bool) (xs : BitString) : Bool :=
  validList pairMode (width xs) (second xs).right && (beforeFlags pairMode xs).all id
end HiddenCircuits.Complexity.EvalValidation.Semantics
