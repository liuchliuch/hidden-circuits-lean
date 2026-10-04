import HiddenCircuits.GraphReduction.Runtime.WordGraph.SampleAtom

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.SampleAtom
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 700000

def kindTag : LetterKind → BitString
  | .R => [true,false,false,false]
  | .D => [false,true,false,false]
  | .B => [false,false,true,false]
  | .E => [false,false,false,true]
def isRight : LetterKind → Bool
  | .R | .D => false
  | .B | .E => true
noncomputable def body (right : Bool) (tag : BitString) : OracleBlock 7 :=
  if right then seq backgrounds (seq (emit tag) (clear 1)) else seq (emit tag) (seq backgrounds (clear 1))

def chunks (right : Bool) (tag : BitString) (i t : ℕ) : BitString :=
  let bg := (List.replicate t (wordChunk [false,false,false,false])).flatten
  let atom := wordChunk (tag++List.replicate i true)
  if right then bg++atom else atom++bg

lemma clear_index (g : BitString → ℕ) (i t : ℕ) (out : BitString) (h : ℕ) :
    (clear (1:Fin 8)).Executes g (state [] (List.replicate i true) t out h) (state [] [] t out h) (i+1) := by
  convert clear_executes g (1:Fin 8) (state [] (List.replicate i true) t out h) using 1
  · funext j;fin_cases j <;> rfl
  · simp [state]

lemma body_executes (g : BitString → ℕ) (right : Bool) (tag : BitString) (i t : ℕ) (out : BitString) (h : ℕ) :
    (body right tag).Executes g (state [] (List.replicate i true) t out h)
      (state [] [] t ((chunks right tag i t).reverse++out) (h+t+1))
      (12*i+9*tag.length+41*t+27) := by
  cases right
  · have ha := emit_executes g tag [] i t out h
    have hb := backgrounds_executes g [] (List.replicate i true) t ((wordChunk (tag++List.replicate i true)).reverse++out) (h+1)
    have hc := clear_index g i t (((List.replicate t (wordChunk [false,false,false,false])).flatten).reverse++((wordChunk (tag++List.replicate i true)).reverse++out)) (h+1+t)
    convert seq_executes _ _ g ha (seq_executes _ _ g hb hc) using 1
    · simp only [chunks,Bool.false_eq_true,ite_false,List.reverse_append,List.append_assoc]
      congr 1
      omega
    · omega
  · have ha := backgrounds_executes g [] (List.replicate i true) t out h
    have hb := emit_executes g tag [] i t (((List.replicate t (wordChunk [false,false,false,false])).flatten).reverse++out) (h+t)
    have hc := clear_index g i t ((wordChunk (tag++List.replicate i true)).reverse++(((List.replicate t (wordChunk [false,false,false,false])).flatten).reverse++out)) (h+t+1)
    convert seq_executes _ _ g ha (seq_executes _ _ g hb hc) using 1
    · simp only [chunks,ite_true,List.reverse_append,List.append_assoc]
    · omega

noncomputable def leftBranch : OracleBlock 7 := branchPop 0 skip (body false (kindTag .R)) (body false (kindTag .D))
noncomputable def rightBranch : OracleBlock 7 := branchPop 0 skip (body true (kindTag .B)) (body true (kindTag .E))
noncomputable def program : OracleBlock 7 := branchPop 0 skip leftBranch rightBranch

lemma pop_kind (b : Bool) (bs index : BitString) (t : ℕ) (out : BitString) (h : ℕ) :
    Function.update (state (b::bs) index t out h) 0 bs=state bs index t out h := by
  funext j;fin_cases j <;> rfl

lemma program_kind_executes (g : BitString → ℕ) (kind : LetterKind) (i t : ℕ) (out : BitString) (h : ℕ) :
    program.Executes g (state (kindBits kind) (List.replicate i true) t out h)
      (state [] [] t ((chunks (isRight kind) (kindTag kind) i t).reverse++out) (h+t+1)) (12*i+41*t+67) := by
  cases kind
  case R =>
    have hb := body_executes g false (kindTag .R) i t out h
    simp only [kindTag,List.length_cons,List.length_nil] at hb
    convert branchPop_false 0 skip leftBranch rightBranch g rfl (s:=state (kindBits .R) (List.replicate i true) t out h) (by
      rw [show kindBits .R=[false,false] from rfl,pop_kind]
      apply branchPop_false 0 skip (body false (kindTag .R)) (body false (kindTag .D)) g rfl
      rw [pop_kind]
      exact hb) using 1 <;> omega
  case D =>
    have hb := body_executes g false (kindTag .D) i t out h
    simp only [kindTag,List.length_cons,List.length_nil] at hb
    convert branchPop_false 0 skip leftBranch rightBranch g rfl (s:=state (kindBits .D) (List.replicate i true) t out h) (by
      rw [show kindBits .D=[false,true] from rfl,pop_kind]
      apply branchPop_true 0 skip (body false (kindTag .R)) (body false (kindTag .D)) g rfl
      rw [pop_kind]
      exact hb) using 1 <;> omega
  case B =>
    have hb := body_executes g true (kindTag .B) i t out h
    simp only [kindTag,List.length_cons,List.length_nil] at hb
    convert branchPop_true 0 skip leftBranch rightBranch g rfl (s:=state (kindBits .B) (List.replicate i true) t out h) (by
      rw [show kindBits .B=[true,false] from rfl,pop_kind]
      apply branchPop_false 0 skip (body true (kindTag .B)) (body true (kindTag .E)) g rfl
      rw [pop_kind]
      exact hb) using 1 <;> omega
  case E =>
    have hb := body_executes g true (kindTag .E) i t out h
    simp only [kindTag,List.length_cons,List.length_nil] at hb
    convert branchPop_true 0 skip leftBranch rightBranch g rfl (s:=state (kindBits .E) (List.replicate i true) t out h) (by
      rw [show kindBits .E=[true,true] from rfl,pop_kind]
      apply branchPop_true 0 skip (body true (kindTag .B)) (body true (kindTag .E)) g rfl
      rw [pop_kind]
      exact hb) using 1 <;> omega

lemma chunks_sample {p : ℕ} (l : Letter (2*p)) (t : ℕ) :
    chunks (isRight l.kind) (kindTag l.kind) l.index.val t=pairStream (sampleLetter l t) := by
  rcases l with ⟨k,i⟩
  cases k <;> simp [chunks,isRight,kindTag,sampleLetter,pairStream_cons,pairStream_append,
    pairStream_replicate,pairAtom,pairTag,cutCode,pairStream_nil]

theorem program_executes {p : ℕ} (g : BitString → ℕ) (l : Letter (2*p)) (t : ℕ) (out : BitString) (h : ℕ) :
    program.Executes g (state (kindBits l.kind) (List.replicate l.index.val true) t out h)
      (state [] [] t ((pairStream (sampleLetter l t)).reverse++out) (h+t+1)) (12*l.index.val+41*t+67) := by
  simpa only [chunks_sample] using program_kind_executes g l.kind l.index.val t out h
end HiddenCircuits.GraphReduction.Runtime.WordGraph.SampleAtom
