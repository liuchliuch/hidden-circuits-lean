import HiddenCircuits.Approximation.SamplerRuntime.GraphDecode
import HiddenCircuits.Complexity.PairSerialization

namespace HiddenCircuits.Approximation.SamplerRuntime.GraphParser
open Complexity OracleBlock
set_option maxHeartbeats 700000

def validationStore (raw value work tmp : BitString) : Store 38 := fun q =>
  if q.val=0 then raw else if q.val=1 then value else if q.val=2 then work else if q.val=3 then tmp else []
noncomputable def falseLoop : OracleBlock 38 := whilePop 2 (push 1 false) (push 1 false)
def pairMap : Fin 3 ↪ Fin 39 where
  toFun q := ⟨q.val+1,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh:=congrArg Fin.val h;dsimp at hh;omega
noncomputable def prepareValidation : OracleBlock 38 := seq (copyOn 0 2 3 (by decide) (by decide) (by decide))
  (seq falseLoop (seq (copyOn 0 2 3 (by decide) (by decide) (by decide)) (PairSerialization.on pairMap)))

lemma false_push (m : ℕ) (xs : BitString) : List.replicate m false++false::xs=List.replicate (m+1) false++xs := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih

lemma falseLoop_executes (g : BitString → ℕ) (raw clock value : BitString) :
    falseLoop.Executes g (validationStore raw value clock [])
      (validationStore raw (List.replicate clock.length false++value) [] []) (3*clock.length+1) := by
  apply whilePop_executes
  induction clock generalizing value with
  | nil => simpa using WhileExecution.empty (validationStore raw value [] []) rfl
  | cons b clock ih =>
    have hpop : Function.update (validationStore raw value (b::clock) []) (2:Fin 39) clock=validationStore raw value clock [] := by
      funext q;fin_cases q <;> rfl
    have hp : (push (1:Fin 39) false).Executes g (validationStore raw value clock [])
        (validationStore raw (false::value) clock []) 1 := by
      convert push_executes g (1:Fin 39) false (validationStore raw value clock []) using 1
      funext q;fin_cases q <;> rfl
    have ht := ih (false::value)
    rw [false_push] at ht
    have hc : 1+1+1+(3*clock.length+1)=3*(b::clock).length+1 := by simp;omega
    rw [←hc]
    cases b
    · exact WhileExecution.zero rfl (by rw [hpop];exact hp) ht
    · exact WhileExecution.one rfl (by rw [hpop];exact hp) ht

theorem prepareValidation_executes (g : BitString → ℕ) (raw : BitString) :
    prepareValidation.Executes g (validationStore raw [] [] []) (validationStore raw (validationInput raw) [] []) (23*raw.length+20) := by
  have h1 : (copyOn (0:Fin 39) 2 3 (by decide) (by decide) (by decide)).Executes g
      (validationStore raw [] [] []) (validationStore raw [] raw []) (5*raw.length+2) := by
    convert copyOn_executes g (0:Fin 39) 2 3 (by decide) (by decide) (by decide) (validationStore raw [] [] []) rfl using 1
    funext q;fin_cases q <;> simp [validationStore]
  have h2 := falseLoop_executes g raw raw []
  simp only [List.append_nil] at h2
  have h3 : (copyOn (0:Fin 39) 2 3 (by decide) (by decide) (by decide)).Executes g
      (validationStore raw (List.replicate raw.length false) [] []) (validationStore raw (List.replicate raw.length false) raw []) (5*raw.length+2) := by
    convert copyOn_executes g (0:Fin 39) 2 3 (by decide) (by decide) (by decide)
      (validationStore raw (List.replicate raw.length false) [] []) rfl using 1
    funext q;fin_cases q <;> simp [validationStore]
  have h4 := PairSerialization.on_executes pairMap g (validationStore raw (List.replicate raw.length false) raw [])
    raw (List.replicate raw.length false) (by funext q;fin_cases q <;> rfl)
  have he : Function.update (Function.update (validationStore raw (List.replicate raw.length false) raw [])
      (pairMap 1) []) (pairMap 0) (pairBits raw (List.replicate raw.length false))=validationStore raw (validationInput raw) [] [] := by
    funext q;fin_cases q <;> rfl
  rw [he] at h4
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)) using 1 <;> omega
lemma prepareValidation_queryFree : prepareValidation.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (whilePop_queryFree _ _ _ (push_queryFree _ _) (push_queryFree _ _))
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (PairSerialization.on_queryFree _)))
end HiddenCircuits.Approximation.SamplerRuntime.GraphParser
