import HiddenCircuits.Complexity.InitialRowFamily

/-! Uniform initial-row traversal using actual finite copy, pop, unary push and
CNF emission instructions. Input, witness-length and height masters are read-only. -/
namespace HiddenCircuits.Complexity.InitialRowEmitter
open OracleBlock TM2BooleanEncoding InitialSourceClassifier

/-- Ports0/1 source and dense target;2/3 work;4 reversed stream;5/6/7 masters
input/witness length/height;8 input copy;9 height remainder;10 witness clock;
11 copy temporary. -/
def state (source target : ℕ) (x : BitString) (m height : ℕ)
    (input : BitString) (remaining witness : ℕ) (stream : BitString) : Store 11 := fun i =>
  if i.val=0 then List.replicate source true else
  if i.val=1 then List.replicate target true else
  if i.val=4 then stream else if i.val=5 then x else
  if i.val=6 then List.replicate m true else if i.val=7 then List.replicate height true else
  if i.val=8 then input else if i.val=9 then List.replicate remaining true else
  if i.val=10 then List.replicate witness true else []

def familyEmbedding : Fin 5 ↪ Fin 12 := Fin.castAddEmb 7

variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def controls : OracleBlock 11 := rename (InitialRowFamily.controlProgram M) familyEmbedding
noncomputable def symbols (mode : Mode) : OracleBlock 11 := rename (InitialRowFamily.symbolProgram M mode) familyEmbedding

def familyBound (source target count : ℕ) : ℕ := count*(64*(source+target+count)+220)+1

lemma familyBound_mono (count : ℕ) {a b c d : ℕ} (ha : a≤c) (hb : b≤d) :
    familyBound a b count ≤ familyBound c d count := by
  unfold familyBound
  have h := Nat.mul_le_mul_left count (show 64*(a+b+count)+220 ≤ 64*(c+d+count)+220 by omega)
  omega

theorem controls_executes (g : BitString → ℕ) (source target : ℕ) (x : BitString) (m H : ℕ)
    (input : BitString) (remaining witness : ℕ) (stream : BitString) :
    ∃ cost, (controls M).Executes g (state source target x m H input remaining witness stream)
      (state source (target+controlBits M.tm) x m H input remaining witness
        ((InitialRowFamily.controlBits M target).reverse++stream)) cost ∧
      cost ≤ familyBound source target (controlBits M.tm) := by
  obtain ⟨c,hc,hb⟩ := InitialRowFamily.controlProgram_executes M g source target stream
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ familyEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 4 rfl).elim

theorem symbols_executes (g : BitString → ℕ) (mode : Mode) (source target : ℕ) (x : BitString) (m H : ℕ)
    (input : BitString) (remaining witness : ℕ) (stream : BitString) :
    ∃ cost, (symbols M mode).Executes g (state source target x m H input remaining witness stream)
      (state source (target+symbolBits M.tm) x m H input remaining witness
        ((InitialRowFamily.symbolBits M mode source target).reverse++stream)) cost ∧
      cost ≤ familyBound source target (symbolBits M.tm) := by
  obtain ⟨c,hc,hb⟩ := InitialRowFamily.symbolProgram_executes M g mode source target stream
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ familyEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 4 rfl).elim

lemma controls_queryFree : (controls M).QueryFree := rename_queryFree _ _ (InitialRowFamily.controlProgram_queryFree M)
lemma symbols_queryFree (mode : Mode) : (symbols M mode).QueryFree := rename_queryFree _ _ (InitialRowFamily.symbolProgram_queryFree M mode)

/-- Pop one height unit, then emit the complete fixed family at that position. -/
noncomputable def slot (mode : Mode) : OracleBlock 11 := branchPop 9 skip (symbols M mode) (symbols M mode)

lemma pop_remaining (source target : ℕ) (x : BitString) (m H : ℕ)
    (input : BitString) (remaining witness : ℕ) (stream : BitString) :
    Function.update (state source target x m H input (remaining+1) witness stream) 9 (List.replicate remaining true) =
      state source target x m H input remaining witness stream := by
  funext i; fin_cases i <;> rfl

theorem slot_executes (g : BitString → ℕ) (mode : Mode) (source target : ℕ) (x : BitString) (m H : ℕ)
    (input : BitString) (remaining witness : ℕ) (stream : BitString) :
    ∃ cost, (slot M mode).Executes g (state source target x m H input (remaining+1) witness stream)
      (state source (target+symbolBits M.tm) x m H input remaining witness
        ((InitialRowFamily.symbolBits M mode source target).reverse++stream)) cost ∧
      cost ≤ familyBound source target (symbolBits M.tm)+2 := by
  obtain ⟨c,hc,hb⟩ := symbols_executes M g mode source target x m H input remaining witness stream
  have he : (state source target x m H input (remaining+1) witness stream) 9 = true::List.replicate remaining true := rfl
  refine ⟨c+2,?_,by omega⟩
  apply branchPop_true _ _ _ _ g he
  rwa [pop_remaining]

lemma slot_queryFree (mode : Mode) : (slot M mode).QueryFree :=
  branchPop_queryFree _ _ _ _ skip_queryFree (symbols_queryFree M mode) (symbols_queryFree M mode)

end HiddenCircuits.Complexity.InitialRowEmitter
