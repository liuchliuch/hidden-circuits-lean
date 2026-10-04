import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock
variable {k : ℕ}
noncomputable def seedFlags : List (Fin (k+1) × Bool) → OracleBlock k
  | [] => skip
  | (i,b)::rest => seq (push i b) (seedFlags rest)
def seededFlags : List (Fin (k+1) × Bool) → Store k → Store k
  | [],s => s
  | (i,b)::rest,s => seededFlags rest (Function.update s i (b::s i))
theorem seedFlags_executes (flags : List (Fin (k+1) × Bool)) (g : BitString → ℕ) (s : Store k) :
    (seedFlags flags).Executes g s (seededFlags flags s) (3*flags.length+1) := by
  induction flags generalizing s with
  | nil => exact skip_executes g s
  | cons f fs ih =>
    rcases f with ⟨i,b⟩
    have h:=seq_executes _ _ g (push_executes g i b s) (ih (Function.update s i (b::s i)))
    convert h using 1 <;> simp [List.length_cons] <;> omega
lemma seedFlags_queryFree (flags : List (Fin (k+1) × Bool)) : (seedFlags flags).QueryFree := by
  induction flags with
  | nil => exact skip_queryFree
  | cons f fs ih => exact seq_queryFree _ _ (push_queryFree _ _) ih
end HiddenCircuits.GraphReduction.Runtime
