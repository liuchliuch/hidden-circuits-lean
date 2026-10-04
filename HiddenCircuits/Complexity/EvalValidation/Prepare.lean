import HiddenCircuits.Complexity.EvalValidation.Header
import HiddenCircuits.Complexity.EvalValidation.ListLoop

namespace HiddenCircuits.Complexity.EvalValidation.Prepare
open OracleBlock GraphVerifier GraphVerifier.Runtime Core
set_option maxHeartbeats 900000
noncomputable def nonempty (pairMode : Bool) : OracleBlock 31 :=
  if pairMode then Header.headCollect 1 true else push 4 true
noncomputable def program (pairMode : Bool) : OracleBlock 31 :=
  seq Header.program (seq takeMask (seq takeMask (nonempty pairMode)))
def output (pairMode : Bool) (xs : BitString) : Store 31 :=
  state xs (Semantics.second xs).right (Semantics.header xs) (Semantics.width xs) (Semantics.beforeFlags pairMode xs) [] []

lemma nonempty_executes (g : BitString→ℕ) (pairMode : Bool) (input data p width flags : BitString) :
    ∃c,(nonempty pairMode).Executes g (state input data p width flags [] [])
      (state input data p width (Semantics.nonemptyFlag pairMode data::flags) [] []) c ∧ c≤6*data.length+15 := by
  cases pairMode
  · refine ⟨1,?_,by omega⟩
    convert push_executes g (4:Fin 32) true (state input data p width flags [] []) using 1
    funext i;fin_cases i <;> rfl
  · obtain ⟨c,hc,hb⟩:=Header.headCollect_executes g 1 true input data p width flags data rfl
    rw [Header.headValue_true] at hc
    exact ⟨c,hc,hb⟩

lemma data_bounds (xs : BitString) :
    (Semantics.header xs).length≤xs.length ∧ (Semantics.width xs).length≤2*xs.length ∧
    (parse xs).right.length≤xs.length ∧ (Semantics.first xs).right.length≤xs.length ∧
    (Semantics.second xs).right.length≤xs.length := by
  have hp:(Semantics.header xs).length≤xs.length:=(parse_lengths xs).1
  have hd:=(parse_lengths xs).2
  have h1:=(Field.lengths (parse xs).right).2
  have h2:=(Field.lengths (Semantics.first xs).right).2
  refine ⟨hp,?_,hd,h1.trans hd,h2.trans (h1.trans hd)⟩
  simp only [Semantics.width,List.length_append]
  omega

theorem program_executes (g : BitString→ℕ) (pairMode : Bool) (xs : BitString) :
    ∃c,(program pairMode).Executes g (Function.update (fun _=>[]) 0 xs) (output pairMode xs) c ∧
      c≤100000*(xs.length+1)^2 := by
  obtain ⟨a,ha,hab⟩:=Header.program_executes g xs
  obtain ⟨b,hb,hbb⟩:=takeMask_executes g xs (parse xs).right (Semantics.header xs) (Semantics.width xs) (Semantics.headerFlags xs)
  obtain ⟨c,hc,hcb⟩:=takeMask_executes g xs (Semantics.first xs).right (Semantics.header xs) (Semantics.width xs)
    (maskFlags (parse xs).right (Semantics.header xs) (Semantics.width xs) (Semantics.headerFlags xs))
  obtain ⟨d,hd,hdb⟩:=nonempty_executes g pairMode xs (Semantics.second xs).right (Semantics.header xs) (Semantics.width xs) (Semantics.parsedFlags xs)
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  obtain ⟨hp,hw,hs,h1,h2⟩:=data_bounds xs
  have hbN:((parse xs).right.length+(Semantics.header xs).length+(Semantics.width xs).length+1)^2≤(4*xs.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hcN:((Semantics.first xs).right.length+(Semantics.header xs).length+(Semantics.width xs).length+1)^2≤(4*xs.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

noncomputable def run (pairMode : Bool) : OracleBlock 31 := seq (program pairMode) (ListLoop.program pairMode)
def finished (pairMode : Bool) (xs : BitString) : Store 31 :=
  state xs [] (Semantics.header xs) (Semantics.width xs)
    (Semantics.runFlags pairMode (Semantics.width xs) (Semantics.second xs).right (Semantics.beforeFlags pairMode xs)) [] []
theorem run_executes (g : BitString→ℕ) (pairMode : Bool) (xs : BitString) :
    ∃c,(run pairMode).Executes g (Function.update (fun _=>[]) 0 xs) (finished pairMode xs) c ∧
      c≤200000*(xs.length+1)^2 := by
  obtain ⟨a,ha,hab⟩:=program_executes g pairMode xs
  obtain ⟨b,hb,hbb⟩:=ListLoop.program_executes g pairMode xs (Semantics.header xs) (Semantics.width xs)
    (Semantics.second xs).right (Semantics.beforeFlags pairMode xs)
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  obtain ⟨hp,hw,hs,h1,h2⟩:=data_bounds xs
  have hbN:((Semantics.second xs).right.length+(Semantics.header xs).length+(Semantics.width xs).length+1)^2≤(4*xs.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith
end HiddenCircuits.Complexity.EvalValidation.Prepare
