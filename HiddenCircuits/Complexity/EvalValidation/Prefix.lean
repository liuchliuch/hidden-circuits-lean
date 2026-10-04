import HiddenCircuits.Complexity.EvalValidation.PairAtom

/-! A fixed finite prefix grammar compiled to real bit branches. None accepts
either data bit; some b checks the literal marker b. -/
namespace HiddenCircuits.Complexity.EvalValidation.Prefix
open OracleBlock
set_option maxHeartbeats 800000
noncomputable def read : List (Option Bool)→OracleBlock 8
  | [] => DirectIndex.program
  | e::es => branchPop 0 PairAtom.reject
    (if e=some true then PairAtom.reject else read es)
    (if e=some false then PairAtom.reject else read es)
def evaluate : List (Option Bool)→BitString→BitString→Bool
  | [],xs,width => Index.valid xs width
  | _::_,[],_ => false
  | e::es,b::xs,width => if e=some (!b) then false else evaluate es xs width

theorem read_executes (g : BitString→ℕ) (pattern : List (Option Bool)) (xs width : BitString) :
    ∃c,(read pattern).Executes g (Index.store xs width [] [] [] [] [])
      (Index.store [] width [evaluate pattern xs width] [] [] [] []) c ∧ c≤100*(xs.length+width.length+1)+2*pattern.length := by
  induction pattern generalizing xs with
  | nil => simpa [read,evaluate] using DirectIndex.program_executes g xs width
  | cons e es ih =>
    cases xs with
    | nil =>
      refine ⟨6,branchPop_empty 0 _ _ _ g rfl (PairAtom.reject_executes g [] width),?_⟩
      simp only [List.length_nil,List.length_cons]
      omega
    | cons b xs =>
      cases b
      · by_cases he:e=some true
        · refine ⟨xs.length+6,?_,?_⟩
          simp only [read,evaluate,Bool.not_false,he,if_true]
          exact branchPop_false 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact PairAtom.reject_executes g xs width)
          simp only [List.length_cons];omega
        · obtain ⟨c,hc,hb⟩:=ih xs
          refine ⟨c+2,?_,?_⟩
          simp only [read,evaluate,Bool.not_false,he,if_false]
          exact branchPop_false 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact hc)
          simp only [List.length_cons];omega
      · by_cases he:e=some false
        · refine ⟨xs.length+6,?_,?_⟩
          simp only [read,evaluate,Bool.not_true,he,if_true]
          exact branchPop_true 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact PairAtom.reject_executes g xs width)
          simp only [List.length_cons];omega
        · obtain ⟨c,hc,hb⟩:=ih xs
          refine ⟨c+2,?_,?_⟩
          simp only [read,evaluate,Bool.not_true,he,if_false]
          exact branchPop_true 0 _ _ _ g rfl (by rw [PairAtom.pop_store];exact hc)
          simp only [List.length_cons];omega
end HiddenCircuits.Complexity.EvalValidation.Prefix
