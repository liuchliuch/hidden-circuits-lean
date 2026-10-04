import HiddenCircuits.DH.Runtime.WordArray
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime

/-! Actual indexed word gathering, one bit-stack iteration. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Gather
open OracleBlock BinaryArithmetic

def state (data : BitString) (start stride count : ℕ) (out : BitString)
    (position clock : ℕ) (word acc : BitString) : Store 13 := fun q =>
  if q.val = 0 then data else if q.val = 1 then List.replicate start true else
  if q.val = 2 then List.replicate stride true else if q.val = 3 then List.replicate count true else
  if q.val = 4 then out else if q.val = 5 then List.replicate position true else
  if q.val = 6 then List.replicate clock true else if q.val = 7 then word else
  if q.val = 8 then acc else []

def store (data : BitString) (start stride count : ℕ) (out : BitString) : Store 13 :=
  state data start stride count out 0 0 [] []

def readPorts : Fin 8 ↪ Fin 14 where
  toFun := ![0,5,7,9,10,11,12,13]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def emitPorts : Fin 2 ↪ Fin 14 where
  toFun := ![7,8]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def read : OracleBlock 13 := DH.Runtime.WordArray.readOn readPorts
noncomputable def emit : OracleBlock 13 := rename wordEmit emitPorts
noncomputable def advance : OracleBlock 13 := copyOn 2 5 9 (by decide) (by decide) (by decide)
noncomputable def body : OracleBlock 13 := seq read (seq emit advance)

def words (ws : List BitString) (position stride : ℕ) : ℕ → List BitString
  | 0 => []
  | count+1 => ws[position]?.getD [] :: words ws (position+stride) stride count

theorem word_length_le (ws : List BitString) (position : ℕ) :
    (ws[position]?.getD []).length ≤ (encodeBitList ws).length := by
  cases h : ws[position]? with
  | none => simp
  | some w =>
    simp only [Option.getD_some]
    exact member_length_le_encodeBitList (List.mem_of_getElem? h)

theorem words_length (ws : List BitString) (position stride count : ℕ) :
    (words ws position stride count).length = count := by
  induction count generalizing position with
  | zero => rfl
  | succ count ih => simp [words, ih]

theorem encoded_words_length (ws : List BitString) (position stride count : ℕ) :
    (encodeBitList (words ws position stride count)).length ≤
      count * (2 * (encodeBitList ws).length + 2) := by
  induction count generalizing position with
  | zero => simp [words, encodeBitList]
  | succ count ih =>
    have h := word_length_le ws position
    have ht := ih (position+stride)
    simp only [words, encodeBitList, List.length_cons, pairBits_length]
    nlinarith

theorem read_executes (g : BitString → ℕ) (ws : List BitString) (start stride count : ℕ)
    (out : BitString) (position clock : ℕ) (acc : BitString) :
    ∃ t, read.Executes g (state (encodeBitList ws) start stride count out position clock [] acc)
      (state (encodeBitList ws) start stride count out position clock (ws[position]?.getD []) acc) t ∧
      t ≤ GraphReduction.Runtime.lookupBound (encodeBitList ws).length position := by
  obtain ⟨t,ht,hb⟩ := DH.Runtime.WordArray.readOn_executes readPorts g
    (state (encodeBitList ws) start stride count out position clock [] acc) ws position
    (by funext i; fin_cases i <;> rfl)
  refine ⟨t, ?_, hb⟩
  have he : Function.update (state (encodeBitList ws) start stride count out position clock [] acc)
      (readPorts 2) (ws[position]?.getD []) =
      state (encodeBitList ws) start stride count out position clock (ws[position]?.getD []) acc := by
    funext i; fin_cases i <;> rfl
  rw [he] at ht
  exact ht

theorem emit_executes (g : BitString → ℕ) (data : BitString) (start stride count : ℕ)
    (out : BitString) (position clock : ℕ) (word acc : BitString) :
    emit.Executes g (state data start stride count out position clock word acc)
      (state data start stride count out position clock [] ((wordChunk word).reverse ++ acc))
      (6*word.length+7) := by
  apply rename_executes_to wordEmit emitPorts g (wordEmit_executes g word acc)
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> first | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | rfl

theorem advance_executes (g : BitString → ℕ) (data : BitString) (start stride count : ℕ)
    (out : BitString) (position clock : ℕ) (acc : BitString) :
    advance.Executes g (state data start stride count out position clock [] acc)
      (state data start stride count out (position+stride) clock [] acc) (5*stride+2) := by
  have h := copyOn_executes g (2 : Fin 14) 5 9 (by decide) (by decide) (by decide)
    (state data start stride count out position clock [] acc) rfl
  have he : Function.update (state data start stride count out position clock [] acc) 5
      (List.replicate stride true ++ List.replicate position true) =
      state data start stride count out (position+stride) clock [] acc := by
    funext i; fin_cases i <;> simp [state, Nat.add_comm]
  change advance.Executes g _ _ _
  simpa only [show state data start stride count out position clock [] acc 2 = List.replicate stride true from rfl,
    show state data start stride count out position clock [] acc 5 = List.replicate position true from rfl,
    List.length_replicate, he] using h

theorem body_executes (g : BitString → ℕ) (ws : List BitString) (start stride count : ℕ)
    (out : BitString) (position clock : ℕ) (acc : BitString) :
    ∃ t, body.Executes g (state (encodeBitList ws) start stride count out position clock [] acc)
      (state (encodeBitList ws) start stride count out (position+stride) clock []
        ((wordChunk (ws[position]?.getD [])).reverse ++ acc)) t ∧
      t ≤ GraphReduction.Runtime.lookupBound (encodeBitList ws).length position +
        6*(encodeBitList ws).length+5*stride+13 := by
  obtain ⟨t,ht,hb⟩ := read_executes g ws start stride count out position clock acc
  have he := emit_executes g (encodeBitList ws) start stride count out position clock (ws[position]?.getD []) acc
  have ha := advance_executes g (encodeBitList ws) start stride count out position clock
    ((wordChunk (ws[position]?.getD [])).reverse ++ acc)
  refine ⟨_, seq_executes _ _ g ht (seq_executes _ _ g he ha), ?_⟩
  have hw := word_length_le ws position
  omega

theorem body_queryFree : body.QueryFree := seq_queryFree _ _
  (DH.Runtime.WordArray.readOn_queryFree _) (seq_queryFree _ _
    (rename_queryFree _ _ wordEmit_queryFree) (copyOn_queryFree _ _ _ _ _ _))

end HiddenCircuits.Complexity.DeterminantRuntime.Gather
