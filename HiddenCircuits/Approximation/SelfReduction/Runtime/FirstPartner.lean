import HiddenCircuits.Complexity.GraphVerifier.TwoParse
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.BitList

/-! Read the first canonical partner word from a sound success-prefixed matching
witness. Empty/failure markers remain distinct from partner zero. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open GraphVerifier

noncomputable def firstPartnerAccept : OracleBlock 3 :=
  seq (clear 0) (seq (moveOn 1 0 2 (by decide) (by decide) (by decide)) (push 0 true))
noncomputable def firstPartnerReject : OracleBlock 3 := seq (clear 0) (clear 1)
noncomputable def firstPartnerRead : OracleBlock 3 :=
  seq GraphVerifier.Runtime.unpairBlock (branchPop 3 firstPartnerReject firstPartnerReject firstPartnerAccept)
noncomputable def firstPartnerWord : OracleBlock 3 :=
  branchPop 0 (clear 0) (clear 0) (branchPop 0 (clear 0) (clear 0) firstPartnerRead)

 def firstPartnerValue : BitString → BitString
  | true::true::rest => if (parse rest).ok then true::(parse rest).left else []
  | _ => []

 theorem firstPartnerAccept_executes (g : BitString → ℕ) (word rest : BitString) :
    firstPartnerAccept.Executes g (GraphVerifier.Runtime.parseStore rest word [] [])
      (GraphVerifier.Runtime.parseStore (true::word) [] [] []) (rest.length+6*word.length+11) := by
  have h1 : (clear (0 : Fin 4)).Executes g (GraphVerifier.Runtime.parseStore rest word [] [])
      (GraphVerifier.Runtime.parseStore [] word [] []) (rest.length+1) := by
    convert clear_executes g (0 : Fin 4) (GraphVerifier.Runtime.parseStore rest word [] []) using 1
    funext i; fin_cases i <;> rfl
  have h2 : (moveOn (1 : Fin 4) 0 2 (by decide) (by decide) (by decide)).Executes g
      (GraphVerifier.Runtime.parseStore [] word [] []) (GraphVerifier.Runtime.parseStore word [] [] [])
      (6*word.length+5) := by
    convert moveOn_executes g (1 : Fin 4) 0 2 (by decide) (by decide) (by decide)
      (GraphVerifier.Runtime.parseStore [] word [] []) rfl using 1
    funext i; fin_cases i <;> simp [GraphVerifier.Runtime.parseStore] <;> rfl
  have h3 : (push (0 : Fin 4) true).Executes g (GraphVerifier.Runtime.parseStore word [] [] [])
      (GraphVerifier.Runtime.parseStore (true::word) [] [] []) 1 := by
    convert push_executes g (0 : Fin 4) true (GraphVerifier.Runtime.parseStore word [] [] []) using 1
    funext i; fin_cases i <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

 theorem firstPartnerReject_executes (g : BitString → ℕ) (word rest : BitString) :
    firstPartnerReject.Executes g (GraphVerifier.Runtime.parseStore rest word [] [])
      (GraphVerifier.Runtime.parseStore [] [] [] []) (rest.length+word.length+4) := by
  have h1 : (clear (0 : Fin 4)).Executes g (GraphVerifier.Runtime.parseStore rest word [] [])
      (GraphVerifier.Runtime.parseStore [] word [] []) (rest.length+1) := by
    convert clear_executes g (0 : Fin 4) (GraphVerifier.Runtime.parseStore rest word [] []) using 1
    funext i; fin_cases i <;> rfl
  have h2 : (clear (1 : Fin 4)).Executes g (GraphVerifier.Runtime.parseStore [] word [] [])
      (GraphVerifier.Runtime.parseStore [] [] [] []) (word.length+1) := by
    convert clear_executes g (1 : Fin 4) (GraphVerifier.Runtime.parseStore [] word [] []) using 1
    funext i; fin_cases i <;> rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

 theorem firstPartnerRead_executes (g : BitString → ℕ) (raw : BitString) :
    ∃ t, firstPartnerRead.Executes g (GraphVerifier.Runtime.parseStore raw [] [] [])
      (GraphVerifier.Runtime.parseStore (if (parse raw).ok then true::(parse raw).left else []) [] [] []) t ∧
      t ≤ 20*raw.length+30 := by
  have hp := GraphVerifier.Runtime.unpairBlock_executes g raw
  have hlen := GraphVerifier.Runtime.parse_lengths raw
  have hcost := GraphVerifier.unpair_cost_bound raw
  have hpop (flag : Bool) : Function.update (GraphVerifier.Runtime.parseStore (parse raw).right (parse raw).left [] [flag])
      (3 : Fin 4) []=GraphVerifier.Runtime.parseStore (parse raw).right (parse raw).left [] [] := by
    funext i; fin_cases i <;> rfl
  cases ho : (parse raw).ok with
  | false =>
    rw [ho] at hp
    have hb := branchPop_false (3 : Fin 4) firstPartnerReject firstPartnerReject firstPartnerAccept g
      (s := GraphVerifier.Runtime.parseStore (parse raw).right (parse raw).left [] [false]) (rest := []) rfl
      (by rw [hpop]; exact firstPartnerReject_executes g _ _)
    refine ⟨(parseCost raw+2*(parse raw).left.length+1)+((parse raw).right.length+(parse raw).left.length+6)+2,?_,?_⟩
    · simpa [firstPartnerRead,ho] using seq_executes _ _ g hp hb
    · omega
  | true =>
    rw [ho] at hp
    have hb := branchPop_true (3 : Fin 4) firstPartnerReject firstPartnerReject firstPartnerAccept g
      (s := GraphVerifier.Runtime.parseStore (parse raw).right (parse raw).left [] [true]) (rest := []) rfl
      (by rw [hpop]; exact firstPartnerAccept_executes g _ _)
    refine ⟨(parseCost raw+2*(parse raw).left.length+1)+((parse raw).right.length+6*(parse raw).left.length+13)+2,?_,?_⟩
    · simpa [firstPartnerRead,ho] using seq_executes _ _ g hp hb
    · omega

 theorem firstPartnerWord_empty (g : BitString → ℕ) :
    firstPartnerWord.Executes g (GraphVerifier.Runtime.parseStore [] [] [] [])
      (GraphVerifier.Runtime.parseStore [] [] [] []) 3 := by
  apply branchPop_empty _ _ _ _ g rfl
  convert clear_executes g (0 : Fin 4) (GraphVerifier.Runtime.parseStore [] [] [] []) using 1
  funext i; fin_cases i <;> rfl

/-- A success-prefixed nonempty witness yields the first word with its success
bit retained, so the empty unary encoding of vertex zero cannot mean failure. -/
theorem firstPartnerWord_success (g : BitString → ℕ) (word : BitString) (rest : List BitString) :
    ∃ t, firstPartnerWord.Executes g (GraphVerifier.Runtime.parseStore (true::encodeBitList (word::rest)) [] [] [])
      (GraphVerifier.Runtime.parseStore (true::word) [] [] []) t ∧
      t ≤ 20*(true::encodeBitList (word::rest)).length+34 := by
  obtain ⟨t,ht,hb⟩ := firstPartnerRead_executes g (pairBits word (encodeBitList rest))
  simp only [GraphVerifier.parse_pair] at ht
  have h1 := branchPop_true (0 : Fin 4) (clear 0) (clear 0) firstPartnerRead g
    (s := GraphVerifier.Runtime.parseStore (true::pairBits word (encodeBitList rest)) [] [] [])
    (rest := pairBits word (encodeBitList rest)) rfl
    (by convert ht using 1; funext i; fin_cases i <;> rfl)
  have h2 := branchPop_true (0 : Fin 4) (clear 0) (clear 0)
    (branchPop 0 (clear 0) (clear 0) firstPartnerRead) g
    (s := GraphVerifier.Runtime.parseStore (true::encodeBitList (word::rest)) [] [] [])
    (rest := encodeBitList (word::rest)) rfl
    (by convert h1 using 1; funext i; fin_cases i <;> rfl)
  refine ⟨t+4,?_,?_⟩
  · convert h2 using 1 <;> omega
  · simp only [encodeBitList,List.length_cons]
    omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
