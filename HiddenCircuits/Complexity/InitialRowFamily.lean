import HiddenCircuits.Complexity.InitialSourceClassifier

/-! Finite initial-row cell families with an actual increasing unary dense
variable index. The fixed machine alphabet is compiled into finite code. -/
namespace HiddenCircuits.Complexity.InitialRowFamily
open OracleBlock InitialCellEmitter TM2BooleanEncoding

noncomputable def advance (B : OracleBlock 4) : OracleBlock 4 := seq B (push 1 true)
noncomputable def walk {α : Type*} (block : α → OracleBlock 4) (items : List α) : OracleBlock 4 :=
  sequence (items.map (fun a => advance (block a)))

def walkBits {α : Type*} (chunk : α → ℕ → BitString) : List α → ℕ → BitString
  | [], _ => []
  | a::as, target => chunk a target ++ walkBits chunk as (target+1)

theorem walk_executes {α : Type*} (g : BitString → ℕ) (block : α → OracleBlock 4)
    (chunk : α → ℕ → BitString) (items : List α) (source : ℕ)
    (hitem : ∀ a ∈ items, ∀ target stream, ∃ cost,
      (block a).Executes g (state source target 0 0 stream)
        (state source target 0 0 ((chunk a target).reverse++stream)) cost ∧
      cost ≤ 64*(source+target)+215) (target : ℕ) (stream : BitString) :
    ∃ cost, (walk block items).Executes g (state source target 0 0 stream)
      (state source (target+items.length) 0 0 ((walkBits chunk items target).reverse++stream)) cost ∧
      cost ≤ items.length*(64*(source+target+items.length)+220)+1 := by
  induction items generalizing target stream with
  | nil => exact ⟨1,by simpa [walk,walkBits,OracleBlock.sequence] using skip_executes g (state source target 0 0 stream),by simp⟩
  | cons a items ih =>
    obtain ⟨ca,ha,hba⟩ := hitem a (by simp) target stream
    have hp : (push (1 : Fin 5) true).Executes g
        (state source target 0 0 ((chunk a target).reverse++stream))
        (state source (target+1) 0 0 ((chunk a target).reverse++stream)) 1 := by
      convert push_executes g (1 : Fin 5) true (state source target 0 0 ((chunk a target).reverse++stream)) using 1
      funext i; fin_cases i <;> simp [state,List.replicate_succ]
    obtain ⟨ct,ht,hbt⟩ := ih (fun b hb => hitem b (List.mem_cons_of_mem _ hb)) (target+1)
      ((chunk a target).reverse++stream)
    refine ⟨ca+1+2+ct+2,?_,?_⟩
    · convert seq_executes _ _ g (seq_executes _ _ g ha hp) ht using 1 <;>
        simp [walk,OracleBlock.sequence,walkBits,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp only [List.length_cons]
      rw [show source+(target+1)+items.length=source+target+(items.length+1) by omega] at hbt
      nlinarith

lemma walk_queryFree {α : Type*} (block : α → OracleBlock 4) (items : List α)
    (h : ∀ a ∈ items, (block a).QueryFree) : (walk block items).QueryFree := by
  apply sequence_queryFree
  intro B hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  exact seq_queryFree _ _ (h a ha) (push_queryFree _ _)

noncomputable def controls (M : Turing.FinTM2) : List (Control M) :=
  List.ofFn (fun i : Fin (controlBits M) => (Fintype.equivFin (Control M)).symm i)
noncomputable def symbols (M : Turing.FinTM2) : List (Symbols M) :=
  List.ofFn (fun i : Fin (symbolBits M) => (symbolEnumeration M).symm i)

@[simp] lemma controls_length (M : Turing.FinTM2) : (controls M).length=controlBits M := by simp [controls]
@[simp] lemma symbols_length (M : Turing.FinTM2) : (symbols M).length=symbolBits M := by simp [symbols]

variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def controlProgram : OracleBlock 4 :=
  walk (fun q => constant (InitialSourceClassifier.controlValue M q)) (controls M.tm)
noncomputable def controlBits (target : ℕ) : BitString :=
  walkBits (fun q i => serializedClause [(i,InitialSourceClassifier.controlValue M q)]) (controls M.tm) target

noncomputable def symbolProgram (mode : InitialSourceClassifier.Mode) : OracleBlock 4 :=
  walk (fun s => InitialSourceClassifier.symbolProgram M s mode) (symbols M.tm)
noncomputable def symbolBits (mode : InitialSourceClassifier.Mode) (source target : ℕ) : BitString :=
  walkBits (fun s i => InitialSourceClassifier.symbolBits M s source i mode) (symbols M.tm) target

theorem controlProgram_executes (g : BitString → ℕ) (source target : ℕ) (stream : BitString) :
    ∃ cost, (controlProgram M).Executes g (state source target 0 0 stream)
      (state source (target+TM2BooleanEncoding.controlBits M.tm) 0 0 ((controlBits M target).reverse++stream)) cost ∧
      cost ≤ TM2BooleanEncoding.controlBits M.tm*
        (64*(source+target+TM2BooleanEncoding.controlBits M.tm)+220)+1 := by
  have hitem (q : Control M.tm) (_ : q ∈ controls M.tm) (target : ℕ) (stream : BitString) :
      ∃ cost, (constant (InitialSourceClassifier.controlValue M q)).Executes g
        (state source target 0 0 stream)
        (state source target 0 0 ((serializedClause [(target,InitialSourceClassifier.controlValue M q)]).reverse++stream)) cost ∧
        cost ≤ 64*(source+target)+215 :=
    ⟨_,constant_executes g _ source target stream,by omega⟩
  simpa only [controls_length] using walk_executes g
    (fun q => constant (InitialSourceClassifier.controlValue M q))
    (fun q i => serializedClause [(i,InitialSourceClassifier.controlValue M q)])
    (controls M.tm) source hitem target stream

theorem symbolProgram_executes (g : BitString → ℕ) (mode : InitialSourceClassifier.Mode)
    (source target : ℕ) (stream : BitString) :
    ∃ cost, (symbolProgram M mode).Executes g (state source target 0 0 stream)
      (state source (target+TM2BooleanEncoding.symbolBits M.tm) 0 0 ((symbolBits M mode source target).reverse++stream)) cost ∧
      cost ≤ TM2BooleanEncoding.symbolBits M.tm*
        (64*(source+target+TM2BooleanEncoding.symbolBits M.tm)+220)+1 := by
  have hitem (s : Symbols M.tm) (_ : s ∈ symbols M.tm) (target : ℕ) (stream : BitString) :
      ∃ cost, (InitialSourceClassifier.symbolProgram M s mode).Executes g
        (state source target 0 0 stream)
        (state source target 0 0 ((InitialSourceClassifier.symbolBits M s source target mode).reverse++stream)) cost ∧
        cost ≤ 64*(source+target)+215 :=
    ⟨_,InitialSourceClassifier.symbolProgram_executes M g s mode source target stream,
      InitialSourceClassifier.symbolCost_bound M s source target mode⟩
  simpa only [symbols_length] using walk_executes g
    (fun s => InitialSourceClassifier.symbolProgram M s mode)
    (fun s i => InitialSourceClassifier.symbolBits M s source i mode)
    (symbols M.tm) source hitem target stream

lemma controlProgram_queryFree : (controlProgram M).QueryFree :=
  walk_queryFree _ _ (fun _ _ => constant_queryFree _)
lemma symbolProgram_queryFree (mode : InitialSourceClassifier.Mode) : (symbolProgram M mode).QueryFree :=
  walk_queryFree _ _ (fun _ _ => InitialSourceClassifier.symbolProgram_queryFree M _ _)

end HiddenCircuits.Complexity.InitialRowFamily
