import HiddenCircuits.Complexity.EvalValidation.DirectIndex
import HiddenCircuits.Complexity.PairEncoding
import HiddenCircuits.Complexity.GraphVerifier.FlatVerifier

/-! Four physical tag-bit branches followed by actual unary-index validation.
Short tags, multiple active tag bits, and nonempty background indices reject. -/
namespace HiddenCircuits.Complexity.EvalValidation.PairAtom
open OracleBlock
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
noncomputable def reject : OracleBlock 8 := seq (clear 0) (push 2 false)
noncomputable def emptyTest : OracleBlock 8 := branchPop 0 (push 2 true) reject reject
noncomputable def leaf (tag : BitString) : OracleBlock 8 :=
  if tag=[false,false,false,false] then emptyTest else if tag.count true=1 then DirectIndex.program else reject
noncomputable def read : ℕ→BitString→OracleBlock 8
  | 0,tag => leaf tag
  | n+1,tag => branchPop 0 reject (read n (tag++[false])) (read n (tag++[true]))
noncomputable def program : OracleBlock 8 := read 4 []
def leafValue (tag xs width : BitString) : Bool :=
  if tag=[false,false,false,false] then xs.isEmpty else if tag.count true=1 then Index.valid xs width else false
def evaluate : ℕ→BitString→BitString→BitString→Bool
  | 0,tag,xs,width => leafValue tag xs width
  | _+1,_,[],_ => false
  | n+1,tag,b::xs,width => evaluate n (tag++[b]) xs width

def valid (xs width : BitString) : Bool := evaluate 4 [] xs width

lemma reject_executes (g : BitString→ℕ) (xs width : BitString) :
    reject.Executes g (Index.store xs width [] [] [] [] []) (Index.store [] width [false] [] [] [] []) (xs.length+4) := by
  have h1:(clear (0:Fin 9)).Executes g (Index.store xs width [] [] [] [] []) (Index.store [] width [] [] [] [] []) (xs.length+1) := by
    convert clear_executes g (0:Fin 9) (Index.store xs width [] [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  have h2:(push (2:Fin 9) false).Executes g (Index.store [] width [] [] [] [] []) (Index.store [] width [false] [] [] [] []) 1 := by
    convert push_executes g (2:Fin 9) false (Index.store [] width [] [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega
lemma pop_store (b : Bool) (xs width : BitString) :
    Function.update (Index.store (b::xs) width [] [] [] [] []) 0 xs=Index.store xs width [] [] [] [] [] := by
  funext i;fin_cases i <;> rfl
lemma emptyTest_executes (g : BitString→ℕ) (xs width : BitString) :
    ∃c,emptyTest.Executes g (Index.store xs width [] [] [] [] []) (Index.store [] width [xs.isEmpty] [] [] [] []) c ∧ c≤xs.length+6 := by
  cases xs with
  | nil =>
    refine ⟨3,branchPop_empty 0 _ _ _ g rfl ?_,by simp⟩
    convert push_executes g (2:Fin 9) true (Index.store [] width [] [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  | cons b xs =>
    have h:=reject_executes g xs width
    cases b
    · exact ⟨xs.length+6,branchPop_false 0 _ _ _ g rfl (by rw [pop_store];exact h),by simp⟩
    · exact ⟨xs.length+6,branchPop_true 0 _ _ _ g rfl (by rw [pop_store];exact h),by simp⟩
lemma leaf_executes (g : BitString→ℕ) (tag xs width : BitString) :
    ∃c,(leaf tag).Executes g (Index.store xs width [] [] [] [] []) (Index.store [] width [leafValue tag xs width] [] [] [] []) c ∧
      c≤100*(xs.length+width.length+1) := by
  unfold leaf leafValue
  split_ifs with he hc
  · obtain ⟨c,hc,hb⟩:=emptyTest_executes g xs width
    exact ⟨c,hc,by omega⟩
  · exact DirectIndex.program_executes g xs width
  · exact ⟨_,reject_executes g xs width,by omega⟩
lemma read_executes (g : BitString→ℕ) (n : ℕ) (tag xs width : BitString) :
    ∃c,(read n tag).Executes g (Index.store xs width [] [] [] [] [])
      (Index.store [] width [evaluate n tag xs width] [] [] [] []) c ∧ c≤100*(xs.length+width.length+1)+2*n := by
  induction n generalizing tag xs with
  | zero => simpa [read,evaluate] using leaf_executes g tag xs width
  | succ n ih =>
    cases xs with
    | nil =>
      exact ⟨6,branchPop_empty 0 _ _ _ g rfl (reject_executes g [] width),by simp only [List.length_nil];omega⟩
    | cons b xs =>
      obtain ⟨c,hc,hb⟩:=ih (tag++[b]) xs
      cases b
      · exact ⟨c+2,branchPop_false 0 _ _ _ g rfl (by rw [pop_store];exact hc),by simp only [List.length_cons];omega⟩
      · exact ⟨c+2,branchPop_true 0 _ _ _ g rfl (by rw [pop_store];exact hc),by simp only [List.length_cons];omega⟩
theorem program_executes (g : BitString→ℕ) (xs width : BitString) :
    ∃c,program.Executes g (Index.store xs width [] [] [] [] []) (Index.store [] width [valid xs width] [] [] [] []) c ∧
      c≤200*(xs.length+width.length+1) := by
  obtain ⟨c,hc,hb⟩:=read_executes g 4 [] xs width
  exact ⟨c,hc,by omega⟩

lemma valid_shape (xs width : BitString) : valid xs width=
    match xs with
    | [false,false,false,false] => true
    | true::false::false::false::ys => Index.valid ys width
    | false::true::false::false::ys => Index.valid ys width
    | false::false::true::false::ys => Index.valid ys width
    | false::false::false::true::ys => Index.valid ys width
    | _ => false := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;> rfl
      | cons c xs =>
        cases xs with
        | nil => cases a <;> cases b <;> cases c <;> rfl
        | cons d xs =>
          cases a <;> cases b <;> cases c <;> cases d <;> cases xs <;> rfl

lemma index_isSome (p : ℕ) (xs width : BitString) (hw : width.length=2*p) :
    (decodePairIndex p xs).isSome=Index.valid xs width := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    unfold decodePairIndex at h
    split_ifs at h with hi hu
    · simp only [Index.valid,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨(GraphVerifier.header_all_true xs).mpr hu,by omega⟩
    all_goals simp at h
  · intro h
    change (xs.all id && decide (xs.length+2≤width.length))=true at h
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨hu,hi⟩ := h
    have hu' := (GraphVerifier.header_all_true xs).mp hu
    have hi' : xs.length<2*p-1 := by
      omega
    simp only [decodePairIndex,dif_pos hi',if_pos hu',Option.isSome_some]
lemma valid_decode (p : ℕ) (xs width : BitString) (hw : width.length=2*p) :
    valid xs width=(decodePairAtom p xs).isSome := by
  rw [valid_shape]
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs =>
      cases xs with
      | nil => cases a <;> cases b <;> rfl
      | cons c xs =>
        cases xs with
        | nil => cases a <;> cases b <;> cases c <;> rfl
        | cons d xs =>
          cases a <;> cases b <;> cases c <;> cases d <;> cases xs <;>
            simp [decodePairAtom,index_isSome p _ width hw]
end HiddenCircuits.Complexity.EvalValidation.PairAtom
