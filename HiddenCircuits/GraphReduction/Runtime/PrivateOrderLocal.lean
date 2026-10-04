import HiddenCircuits.GraphReduction.Runtime.PrivateOrderDefs

/-! Exact local order tests in one actual private endpoint block. -/
namespace HiddenCircuits.GraphReduction.Runtime.PrivateOrder
open PrivateProbe

def localRecord {p s : ℕ} (P : CutPair p) : BlockContent (2*p) s → VertexRecord
  | .inl (.inl u) => ⟨false,false,0,u.val,backgroundCode⟩
  | .inl (.inr u) => ⟨true,false,0,u.val,cutCode P⟩
  | .inr (.inl q) => ⟨false,true,0,q.val,backgroundCode⟩
  | .inr (.inr q) => ⟨true,true,0,q.val,backgroundCode⟩
lemma top_even_odd {p s : ℕ} (P : CutPair p) (u v : Fin (2*p)) :
    (top P.upperMode s (.inl (.inl u))).val<(top P.upperMode s (.inl (.inr v))).val ↔ P.first u v≠1 := by
  have he : (top P.upperMode s (.inl (.inl u))).val≠(top P.upperMode s (.inl (.inr v))).val := by
    intro h
    have hh := (top P.upperMode s).injective (Fin.ext h)
    cases hh
  have hc := top_cut (s:=s) P u v
  change _ ↔ ¬(_=1)
  rw [←hc]
  omega
lemma bottom_odd_even {p s : ℕ} (P : CutPair p) (u v : Fin (2*p)) :
    (bottom P.lowerMode s (.inl (.inr u))).val<(bottom P.lowerMode s (.inl (.inl v))).val ↔ P.second u v≠1 := by
  have he : (bottom P.lowerMode s (.inl (.inr u))).val≠(bottom P.lowerMode s (.inl (.inl v))).val := by
    intro h
    have hh := (bottom P.lowerMode s).injective (Fin.ext h)
    cases hh
  have hc := bottom_cut (s:=s) P u v
  change _ ↔ ¬(_=1)
  rw [←hc]
  omega

lemma upperLocal_correct {p s : ℕ} (P : CutPair p) (x y : BlockContent (2*p) s) :
    upperLocalLT (localRecord P x) (localRecord P y)=decide ((top P.upperMode s x).val<(top P.upperMode s y).val) := by
  rcases x with (u|u)|(q|q) <;> rcases y with (v|v)|(r|r)
  all_goals try simp only [localRecord,upperLocalLT,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
    Bool.not_false,Bool.not_true,Bool.and_false,Bool.false_and,Bool.true_and,Bool.and_true,beq_self_eq_true,
    (show (false==true)=false from rfl),(show (true==false)=false from rfl),cutBit_first,
    top_even_lt_iff,top_odd_lt_iff,top_cut,top_even_odd]
  all_goals try simp only [top_even,top_odd,top_evenProbe,top_oddProbe]
  all_goals try have hu := P.upperMode.evenOffset_lt u
  all_goals try have hu' := P.upperMode.oddOffset_lt u
  all_goals try have hv := P.upperMode.evenOffset_lt v
  all_goals try have hv' := P.upperMode.oddOffset_lt v
  all_goals try have hq := q.isLt
  all_goals try have hr := r.isLt
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals try simp only [Bool.false_eq_true,Bool.not_eq_true,decide_eq_true_eq,decide_eq_false_iff_not,iff_false,iff_true]
  all_goals try simp_all
  all_goals omega

lemma lowerLocal_correct {p s : ℕ} (P : CutPair p) (x y : BlockContent (2*p) s) :
    lowerLocalLT (localRecord P x) (localRecord P y)=decide ((bottom P.lowerMode s x).val<(bottom P.lowerMode s y).val) := by
  rcases x with (u|u)|(q|q) <;> rcases y with (v|v)|(r|r)
  all_goals try simp only [localRecord,lowerLocalLT,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
    Bool.not_false,Bool.not_true,Bool.and_false,Bool.false_and,Bool.true_and,Bool.and_true,beq_self_eq_true,
    (show (false==true)=false from rfl),(show (true==false)=false from rfl),cutBit_second,
    bottom_even_lt_iff,bottom_odd_lt_iff,bottom_cut,bottom_odd_even]
  all_goals try simp only [bottom_even,bottom_odd,bottom_evenProbe,bottom_oddProbe]
  all_goals try have hu := P.lowerMode.evenOffset_lt u
  all_goals try have hu' := P.lowerMode.oddOffset_lt u
  all_goals try have hv := P.lowerMode.evenOffset_lt v
  all_goals try have hv' := P.lowerMode.oddOffset_lt v
  all_goals try have hq := q.isLt
  all_goals try have hr := r.isLt
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals try simp only [Bool.false_eq_true,Bool.not_eq_true,decide_eq_true_eq,decide_eq_false_iff_not,iff_false,iff_true]
  all_goals try simp_all
  all_goals omega
end HiddenCircuits.GraphReduction.Runtime.PrivateOrder
