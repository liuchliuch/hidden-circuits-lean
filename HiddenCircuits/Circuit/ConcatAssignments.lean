import HiddenCircuits.Circuit.BitAssignments
import HiddenCircuits.LogicalConcat

/-! Literal Boolean coordinate lookup under logical concatenation. -/
namespace HiddenCircuits.Circuit

/-- Total coordinate lookup, false outside the finite logical word. -/
def bitAt : (n : ℕ) → CodeBits n → ℕ → Bool
  | 0,_,_ => false
  | n+1,x,0 => finBitBool x.1
  | n+1,x,t+1 => bitAt n x.2 t

lemma bitAt_eq_assignment (n : ℕ) (x : CodeBits n) (i : Fin n) :
    bitAt n x i.val=bitsToAssignment n x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih x.2 j

lemma bitAt_concatCore (a b : ℕ) (x : CodeBits a) (y : CodeBits b) (t : ℕ) :
    bitAt (concatSize a b) (concatCore a b x y) t =
      if t<a then bitAt a x t else bitAt b y (t-a) := by
  induction a generalizing t with
  | zero => simp [concatSize,concatCore]
  | succ a ih =>
    cases t with
    | zero => rfl
    | succ t => simpa only [concatSize,concatCore,bitAt,Nat.add_lt_add_iff_right,Nat.add_sub_add_right]
        using ih x.2 t

lemma bitAt_cast {a b : ℕ} (h : a=b) (x : CodeBits a) (t : ℕ) :
    bitAt b (cast (congrArg CodeBits h) x) t=bitAt a x t := by subst b; rfl

theorem bitAt_concat (a b : ℕ) (x : CodeBits a) (y : CodeBits b) (t : ℕ) :
    bitAt (a+b) (codeConcat a b x y) t =
      if t<a then bitAt a x t else bitAt b y (t-a) := by
  change bitAt (a+b) (cast (congrArg CodeBits (concatSize_eq a b)) (concatCore a b x y)) t = _
  rw [bitAt_cast (concatSize_eq a b),bitAt_concatCore]

/-- Every prefix coordinate is the original left bit, with actual Fin index transport. -/
theorem assignment_concat_left (a b : ℕ) (x : CodeBits a) (y : CodeBits b) (i : Fin a) :
    bitsToAssignment (a+b) (codeConcat a b x y) (Fin.castAdd b i)=bitsToAssignment a x i := by
  rw [← bitAt_eq_assignment,← bitAt_eq_assignment]
  change bitAt (a+b) (codeConcat a b x y) i.val=bitAt a x i.val
  rw [bitAt_concat,if_pos i.isLt]

/-- Every suffix coordinate is the original right bit at its explicitly shifted position. -/
theorem assignment_concat_right (a b : ℕ) (x : CodeBits a) (y : CodeBits b) (i : Fin b) :
    bitsToAssignment (a+b) (codeConcat a b x y) (Fin.natAdd a i)=bitsToAssignment b y i := by
  rw [← bitAt_eq_assignment,← bitAt_eq_assignment]
  change bitAt (a+b) (codeConcat a b x y) (a+i.val)=bitAt b y i.val
  rw [bitAt_concat,if_neg (by omega),Nat.add_sub_cancel_left]

end HiddenCircuits.Circuit
