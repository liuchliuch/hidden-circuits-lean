import HiddenCircuits.Complexity.NativeValidation.OneIndex
import HiddenCircuits.Complexity.DeltaEncoding

/-! The literal four-bit gate tag is parsed by nine actual bit branches,
including its four markers and terminator; placements are checked physically. -/
namespace HiddenCircuits.Complexity.NativeValidation.Gate
open OracleBlock EvalValidation Circuit Circuit.Runtime
set_option maxHeartbeats 900000
noncomputable def leaf (deltaMode : Bool) (tag : BitString) : OracleBlock 8 :=
  match decodeTag tag with
  | none=>PairAtom.reject
  | some t=>if deltaMode && decide (t=.controlledSign) then PairAtom.reject else
      if t.width=1 then OneIndex.program else DirectIndex.program
def leafValue (deltaMode : Bool) (tag xs width : BitString) : Bool :=
  match decodeTag tag with
  | none=>false
  | some t=>if deltaMode && decide (t=.controlledSign) then false else
      xs.all id && decide (xs.length+t.width≤width.length)
noncomputable def read (deltaMode : Bool) : ℕ→BitString→OracleBlock 8
  | 0,tag=>branchPop 0 PairAtom.reject (leaf deltaMode tag) PairAtom.reject
  | n+1,tag=>branchPop 0 PairAtom.reject PairAtom.reject
      (branchPop 0 PairAtom.reject (read deltaMode n (tag++[false])) (read deltaMode n (tag++[true])))
def evaluate (deltaMode : Bool) : ℕ→BitString→BitString→BitString→Bool
  | 0,tag,false::xs,width=>leafValue deltaMode tag xs width
  | n+1,tag,true::b::xs,width=>evaluate deltaMode n (tag++[b]) xs width
  | _,_,_,_=>false
noncomputable def program (deltaMode : Bool) : OracleBlock 8 := read deltaMode 4 []
def valid (deltaMode : Bool) (xs width : BitString) : Bool := evaluate deltaMode 4 [] xs width

lemma leaf_executes (g : BitString→ℕ) (deltaMode : Bool) (tag xs width : BitString) :
    ∃c,(leaf deltaMode tag).Executes g (Index.store xs width [] [] [] [] [])
      (Index.store [] width [leafValue deltaMode tag xs width] [] [] [] []) c ∧ c≤210*(xs.length+width.length+1) := by
  unfold leaf leafValue
  cases ht:decodeTag tag with
  | none=>exact ⟨_,PairAtom.reject_executes g xs width,by omega⟩
  | some t=>
    simp only []
    split_ifs with hd hw
    · exact ⟨_,PairAtom.reject_executes g xs width,by omega⟩
    · simpa only [hw] using OneIndex.program_executes g xs width
    · have he:t.width=2:=by cases t <;> simp_all [GateTag.width]
      obtain ⟨c,hc,hb⟩:=DirectIndex.program_executes g xs width
      exact ⟨c,by simpa only [he,Index.valid] using hc,by omega⟩

lemma read_executes (g : BitString→ℕ) (deltaMode : Bool) (n : ℕ) (tag xs width : BitString) :
    ∃c,(read deltaMode n tag).Executes g (Index.store xs width [] [] [] [] [])
      (Index.store [] width [evaluate deltaMode n tag xs width] [] [] [] []) c ∧
      c≤210*(xs.length+width.length+1)+4*n+2 := by
  induction n generalizing tag xs with
  | zero=>
    cases xs with
    | nil=>exact ⟨6,branchPop_empty 0 _ _ _ g rfl (PairAtom.reject_executes g [] width),by simp;omega⟩
    | cons b xs=>
      cases b
      · obtain ⟨c,hc,hb⟩:=leaf_executes g deltaMode tag xs width
        exact ⟨c+2,branchPop_false 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact hc),by simp only [List.length_cons];omega⟩
      · exact ⟨_,branchPop_true 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact PairAtom.reject_executes g xs width),by simp only [List.length_cons];omega⟩
  | succ n ih=>
    cases xs with
    | nil=>exact ⟨6,branchPop_empty 0 _ _ _ g rfl (PairAtom.reject_executes g [] width),by simp;omega⟩
    | cons a xs=>
      cases a
      · exact ⟨_,branchPop_false 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact PairAtom.reject_executes g xs width),by simp only [List.length_cons];omega⟩
      · cases xs with
        | nil=>
          refine ⟨8,branchPop_true 0 _ _ _ g rfl ?_,by simp;omega⟩
          rw [PairAtom.pop_store]
          exact branchPop_empty 0 _ _ _ g rfl (PairAtom.reject_executes g [] width)
        | cons b xs=>
          obtain ⟨c,hc,hb⟩:=ih (tag++[b]) xs
          refine ⟨c+4,branchPop_true 0 _ _ _ g rfl ?_,by simp only [List.length_cons];omega⟩
          rw [PairAtom.pop_store]
          cases b
          · exact branchPop_false 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact hc)
          · exact branchPop_true 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact hc)
theorem program_executes (g : BitString→ℕ) (deltaMode : Bool) (xs width : BitString) :
    ∃c,(program deltaMode).Executes g (Index.store xs width [] [] [] [] [])
      (Index.store [] width [valid deltaMode xs width] [] [] [] []) c ∧ c≤250*(xs.length+width.length+1) := by
  obtain ⟨c,hc,hb⟩:=read_executes g deltaMode 4 [] xs width
  exact ⟨c,hc,by omega⟩
end HiddenCircuits.Complexity.NativeValidation.Gate
