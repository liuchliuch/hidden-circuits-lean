import HiddenCircuits.Complexity.GraphVerifier.TwoParse
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! A strict all-raw list-field parser: check the leading list marker and the
self-delimiting pair terminator, while exposing the exact parsed word and tail. -/
namespace HiddenCircuits.Complexity.EvalValidation.Field
open OracleBlock GraphVerifier GraphVerifier.Runtime
set_option maxHeartbeats 700000

lemma tail_bound (xs : BitString) : xs.tail.length≤xs.length := by cases xs <;> simp

def marker (xs : BitString) : Bool := xs.head?.getD false
def item (xs : BitString) : ParseResult := parse xs.tail
def valid (xs : BitString) : Bool := (item xs).ok && marker xs
def store (xs atom out tmp flag marked : BitString) : Store 5 := ![xs,atom,out,tmp,flag,marked]
def parsePorts : Fin 4 ↪ Fin 6 where
  toFun i:=![0,1,3,4] i
  inj' := by decide +kernel
noncomputable def popMarker : OracleBlock 5 := branchPop 0 (push 5 false) (push 5 false) (push 5 true)
noncomputable def program : OracleBlock 5 := seq popMarker (seq (unpairOn parsePorts) (decision 2 [4,5] (fun bs=>bs.all id)))

lemma popMarker_executes (g : BitString→ℕ) (xs : BitString) :
    popMarker.Executes g (store xs [] [] [] [] []) (store xs.tail [] [] [] [] [marker xs]) 3 := by
  cases xs with
  | nil =>
    apply branchPop_empty 0 _ _ _ g rfl
    convert push_executes g (5:Fin 6) false (store [] [] [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  | cons b xs =>
    have he:Function.update (store (b::xs) [] [] [] [] []) (0:Fin 6) xs=store xs [] [] [] [] [] := by
      funext i;fin_cases i <;> rfl
    have hp:(push (5:Fin 6) b).Executes g (store xs [] [] [] [] []) (store xs [] [] [] [] [b]) 1 := by
      convert push_executes g (5:Fin 6) b (store xs [] [] [] [] []) using 1
      funext i;fin_cases i <;> rfl
    cases b
    · exact branchPop_false 0 _ _ _ g rfl (by rw [he];exact hp)
    · exact branchPop_true 0 _ _ _ g rfl (by rw [he];exact hp)

theorem program_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,program.Executes g (store xs [] [] [] [] [])
      (store (item xs).right (item xs).left [valid xs] [] [] []) c ∧ c≤3*xs.length+19 := by
  let r:=item xs
  let s1:=store xs.tail [] [] [] [] [marker xs]
  let s2:=store r.right r.left [] [] [r.ok] [marker xs]
  have hp:(unpairOn parsePorts).Executes g s1 s2 (parseCost xs.tail+2*r.left.length+1) := by
    apply unpairOn_executes parsePorts g s1 s2 xs.tail
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim
  have hd:(decision (2:Fin 6) [4,5] (fun bs=>bs.all id)).Executes g s2
      (store r.right r.left [valid xs] [] [] []) 8 := by
    have h:=decision_executes (2:Fin 6) [4,5] (by decide) (by decide) (fun bs=>bs.all id)
      (fun i=>if i=4 then r.ok else marker xs) g s2 (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl <;> rfl)
    convert h using 1
    funext i;fin_cases i <;> simp [eraseStore,s2,store,valid,r]
  refine ⟨_,seq_executes _ _ g (popMarker_executes g xs) (seq_executes _ _ g hp hd),?_⟩
  have hc:=unpair_cost_bound xs.tail
  have hl:xs.tail.length≤xs.length:=tail_bound xs
  dsimp only [r,item]
  omega
lemma lengths (xs : BitString) : (item xs).left.length≤xs.length ∧ (item xs).right.length≤xs.length :=
  ⟨(parse_lengths xs.tail).1.trans (tail_bound xs),(parse_lengths xs.tail).2.trans (tail_bound xs)⟩
lemma tail_shorter (b : Bool) (xs : BitString) : (parse xs).right.length<(b::xs).length := by
  have h:=(parse_lengths xs).2
  simp only [List.length_cons]
  omega
end HiddenCircuits.Complexity.EvalValidation.Field
