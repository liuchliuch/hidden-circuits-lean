import HiddenCircuits.Complexity.CNFCloneEmitter.ClauseLookup
import HiddenCircuits.Complexity.GraphVerifier.TwoParse

/-! A total permissive interpretation of word-list bytes. The marker is consumed
on every iteration, so even malformed inputs have a linear number of fields. -/
namespace HiddenCircuits.Complexity.LooseWordList
open GraphVerifier GraphVerifier.Runtime

def words : BitString → List BitString
  | [] => []
  | _::xs => (parse xs).left::words (parse xs).right
termination_by xs=>xs.length
decreasing_by have h:=(parse_lengths xs).2;simp only [List.length_cons];omega

def head : BitString → BitString | []=>[] | _::xs=>(parse xs).left
def tail : BitString → BitString | []=>[] | _::xs=>(parse xs).right

def drop : ℕ → BitString → BitString | 0,xs=>xs | n+1,xs=>drop n (tail xs)

@[simp] theorem words_nil : words []=[] := by rw [words]
@[simp] theorem words_cons (b : Bool) (xs : BitString) : words (b::xs)=(parse xs).left::words (parse xs).right := by rw [words]
lemma tail_length (xs : BitString) : (tail xs).length≤xs.length := by
  cases xs with
  | nil => rfl
  | cons b xs => exact (parse_lengths xs).2.trans (by simp)
lemma drop_length (n : ℕ) (xs : BitString) : (drop n xs).length≤xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => exact (ih (tail xs)).trans (tail_length xs)
lemma words_tail (xs : BitString) : words (tail xs)=(words xs).tail := by cases xs <;> simp [tail]
lemma words_drop (n : ℕ) (xs : BitString) : words (drop n xs)=(words xs).drop n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp only [drop,ih,words_tail,List.drop_tail]
lemma words_head (xs : BitString) : (words xs).head?.getD []=head xs := by cases xs <;> simp [head]
lemma words_length (xs : BitString) : (words xs).length≤xs.length := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => simp
    | cons b bs =>
      have hb:=(parse_lengths bs).2
      have h:=ih (parse bs).right (by change (parse bs).right.length<(b::bs).length;simp;omega)
      simp only [words_cons,List.length_cons]
      omega
lemma word_length (xs w : BitString) (hw:w∈words xs) : w.length≤xs.length := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => simp at hw
    | cons b bs =>
      simp only [words_cons,List.mem_cons] at hw
      rcases hw with rfl|hw
      · exact (parse_lengths bs).1.trans (by simp)
      · have hb:=(parse_lengths bs).2
        exact (ih (parse bs).right (by change (parse bs).right.length<(b::bs).length;simp;omega) hw).trans (by simp;omega)
@[simp] theorem words_encode (ws : List BitString) : words (encodeBitList ws)=ws := by
  induction ws with
  | nil => simp [encodeBitList]
  | cons w ws ih => simp [encodeBitList,ih]

end HiddenCircuits.Complexity.LooseWordList
