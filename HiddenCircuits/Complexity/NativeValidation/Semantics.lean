import HiddenCircuits.Complexity.NativeValidation.Gate
import HiddenCircuits.Complexity.EvalValidation.Field

/-! All-raw semantics shared by the actual native Constraint/Delta validators.
The Boolean mode rejects controlledSign exactly for Delta inputs. -/
namespace HiddenCircuits.Complexity.NativeValidation.Semantics
open GraphVerifier
def validList (deltaMode : Bool) (width : BitString) : BitString→Bool
  | [] => true
  | b::bs => let r:=parse bs
    (r.ok && b) && Gate.valid deltaMode r.left width && validList deltaMode width r.right
termination_by xs=>xs.length
decreasing_by exact EvalValidation.Field.tail_shorter _ _

def runFlags (deltaMode : Bool) (width : BitString) : BitString→BitString→BitString
  | [],flags => flags
  | b::bs,flags => let r:=parse bs
    runFlags deltaMode width r.right (Gate.valid deltaMode r.left width::(r.ok && b)::flags)
termination_by xs _=>xs.length
decreasing_by exact EvalValidation.Field.tail_shorter _ _

lemma runFlags_all (deltaMode : Bool) (width xs flags : BitString) :
    (runFlags deltaMode width xs flags).all id= (validList deltaMode width xs && flags.all id) := by
  induction xs using (measure List.length).wf.induction generalizing flags with
  | h xs ih =>
    cases xs with
    | nil => simp [runFlags,validList]
    | cons b bs =>
      rw [runFlags,ih (parse bs).right (EvalValidation.Field.tail_shorter b bs),validList]
      simp [Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]

def first (xs : BitString) : ParseResult := parse xs
def second (xs : BitString) : ParseResult := parse (first xs).right
def third (xs : BitString) : ParseResult := parse (second xs).right
def source (xs : BitString) : BitString := (first xs).left
def target (xs : BitString) : BitString := (second xs).left
def header (xs : BitString) : BitString := (third xs).left
def payload (xs : BitString) : BitString := (third xs).right
def flags (xs : BitString) : BitString :=
  [decide ((target xs).length=(header xs).length),
   decide ((source xs).length=(header xs).length),(header xs).all id,
   (third xs).ok,(second xs).ok,(first xs).ok]
def test (deltaMode : Bool) (xs : BitString) : Bool :=
  validList deltaMode (header xs) (payload xs) && (flags xs).all id
end HiddenCircuits.Complexity.NativeValidation.Semantics
