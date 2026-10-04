import HiddenCircuits.Complexity.InitialCellCorrectness
import HiddenCircuits.Complexity.TM2InitialSources

/-! Fixed Boolean-map classification of every initial TM2 code cell, compiled
from the actual four unary Boolean maps into finite constant/equivalence emitters.
No variable index is built into the program: the witness index is a unary port. -/
namespace HiddenCircuits.Complexity.InitialSourceClassifier
open OracleBlock TM2BooleanEncoding InitialCellEmitter

noncomputable def unaryProgram (f : Bool → Bool) : OracleBlock 4 :=
  if f false = f true then constant (f false) else bit (f false)

noncomputable def unaryBits (source target : ℕ) (f : Bool → Bool) : BitString :=
  if f false = f true then serializedClause [(target,f false)] else bitBits source target (f false)

noncomputable def unaryCost (source target : ℕ) (f : Bool → Bool) : ℕ :=
  if f false = f true then 32*target+56 else 64*(source+target)+215

theorem unaryProgram_executes (g : BitString → ℕ) (f : Bool → Bool)
    (source target : ℕ) (stream : BitString) :
    (unaryProgram f).Executes g (state source target 0 0 stream)
      (state source target 0 0 ((unaryBits source target f).reverse++stream)) (unaryCost source target f) := by
  unfold unaryProgram unaryBits unaryCost
  split_ifs
  · exact constant_executes _ _ _ _ _
  · exact bit_executes _ _ _ _ _

lemma unaryCost_bound (source target : ℕ) (f : Bool → Bool) :
    unaryCost source target f ≤ 64*(source+target)+215 := by
  unfold unaryCost
  split_ifs <;> omega

lemma unaryProgram_queryFree (f : Bool → Bool) : (unaryProgram f).QueryFree := by
  unfold unaryProgram
  split_ifs
  · exact constant_queryFree _
  · exact bit_queryFree _

lemma unaryBits_eq {p : ℕ} (i : Fin p) (target : ℕ) (f : Bool → Bool) :
    unaryBits i.val target f = InitialCellEmitter.bits target (InputSource.unary i f) := by
  unfold unaryBits InputSource.unary
  split_ifs <;> rfl

lemma map_const {p : ℕ} (s : InputSource p) (b : Bool) :
    s.map (fun _ => b) = InputSource.constant b := by
  cases s <;> simp [InputSource.map,InputSource.unary]

variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def controlValue (q : Control M.tm) : Bool := by
  classical
  exact decide ((some M.tm.main,M.tm.initialState)=q)

noncomputable def emptyValue (s : Symbols M.tm) : Bool := by
  classical
  exact decide ((none : Option (M.tm.Γ s.1))=s.2.map Subtype.val)

noncomputable def symbolMap (s : Symbols M.tm) (b : Bool) : Bool := by
  classical
  exact if hk : s.1=M.tm.k₀ then
    decide (some (M.inputAlphabet.invFun b)=(hk ▸ s.2 : Option (Symbol M.tm M.tm.k₀)).map Subtype.val)
    else emptyValue M s

/-- Classification agrees with the actual initial TM2 source construction,
including every non-input stack and empty-marker symbol. -/
theorem cellSource_symbol {p H : ℕ} (sources : List (InputSource p))
    (i : Fin H) (s : Symbols M.tm) :
    VerifierTableau.cellSource M H sources (Sum.inr ⟨s.1,(i,s.2)⟩) =
      match sources[i.val]? with
      | none => InputSource.constant (emptyValue M s)
      | some src => src.map (symbolMap M s) := by
  classical
  rcases s with ⟨k,a⟩
  by_cases hk : k=M.tm.k₀
  · subst k
    have hf : symbolMap M ⟨M.tm.k₀,a⟩ = (fun b => decide (some (M.inputAlphabet.invFun b)=a.map Subtype.val)) := by
      funext b; simp [symbolMap]
    cases hs : sources[i.val]? <;>
      simp [VerifierTableau.cellSource,emptyValue,hs,hf]
  · have hf : symbolMap M ⟨k,a⟩ = (fun _ => emptyValue M ⟨k,a⟩) := by
      funext b; simp [symbolMap,hk]
    cases hs : sources[i.val]? with
    | none => simp [VerifierTableau.cellSource,symbolMap,emptyValue,hk,hs]
    | some src => simp [VerifierTableau.cellSource,hk,hs,hf,map_const,emptyValue]

lemma cellSource_control {p H : ℕ} (sources : List (InputSource p)) (q : Control M.tm) :
    VerifierTableau.cellSource M H sources (Sum.inl q) =
      InputSource.constant (controlValue M q) := rfl

inductive Mode
  | empty
  | value (b : Bool)
  | witness

noncomputable def symbolProgram (s : Symbols M.tm) : Mode → OracleBlock 4
  | .empty => constant (emptyValue M s)
  | .value b => constant (symbolMap M s b)
  | .witness => unaryProgram (symbolMap M s)

noncomputable def symbolBits (s : Symbols M.tm) (source target : ℕ) : Mode → BitString
  | .empty => serializedClause [(target,emptyValue M s)]
  | .value b => serializedClause [(target,symbolMap M s b)]
  | .witness => unaryBits source target (symbolMap M s)

noncomputable def symbolCost (s : Symbols M.tm) (source target : ℕ) : Mode → ℕ
  | .empty => 32*target+56
  | .value _ => 32*target+56
  | .witness => unaryCost source target (symbolMap M s)

theorem symbolProgram_executes (g : BitString → ℕ) (s : Symbols M.tm) (mode : Mode)
    (source target : ℕ) (stream : BitString) :
    (symbolProgram M s mode).Executes g (state source target 0 0 stream)
      (state source target 0 0 ((symbolBits M s source target mode).reverse++stream))
      (symbolCost M s source target mode) := by
  cases mode with
  | empty => exact constant_executes _ _ _ _ _
  | value b => exact constant_executes _ _ _ _ _
  | witness => exact unaryProgram_executes _ _ _ _ _

lemma symbolCost_bound (s : Symbols M.tm) (source target : ℕ) (mode : Mode) :
    symbolCost M s source target mode ≤ 64*(source+target)+215 := by
  cases mode with
  | empty => dsimp [symbolCost]; omega
  | value b => dsimp [symbolCost]; omega
  | witness => exact unaryCost_bound _ _ _

lemma symbolProgram_queryFree (s : Symbols M.tm) (mode : Mode) :
    (symbolProgram M s mode).QueryFree := by
  cases mode with
  | empty => exact constant_queryFree _
  | value b => exact constant_queryFree _
  | witness => exact unaryProgram_queryFree _

lemma symbolBits_witness {p : ℕ} (s : Symbols M.tm) (i : Fin p) (target : ℕ) :
    symbolBits M s i.val target .witness =
      InitialCellEmitter.bits target ((InputSource.bit i false).map (symbolMap M s)) := by
  simpa [symbolBits,InputSource.map] using unaryBits_eq i target (symbolMap M s)

end HiddenCircuits.Complexity.InitialSourceClassifier
