import HiddenCircuits.Circuit.Runtime.GateEmitter
import HiddenCircuits.Circuit.Runtime.UniformGateSemantics

/-! Actual increasing-position scan for the source preparation/reset gates. -/
namespace HiddenCircuits.Circuit.Runtime.UniformGateEmitter
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def store (n p r : ℕ) (stream : BitString) : Store 5 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then List.replicate p true else
  if i.val=2 then List.replicate r true else if i.val=3 then stream else []

def atomEmbedding : Fin 4 ↪ Fin 6 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 3 else if i.val=2 then 5 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def atom (tag : GateTag) : OracleBlock 5 := rename (GateEmitter.atom tag) atomEmbedding
noncomputable def body (tag : GateTag) : OracleBlock 5 := seq (atom tag) (push 1 true)
noncomputable def loop (tag : GateTag) : OracleBlock 5 := whilePop 2 (body tag) (body tag)

def chunks (tag : GateTag) (p r : ℕ) : BitString :=
  (List.range' p r).flatMap (GateEmitter.chunk tag)

lemma body_executes (g : BitString → ℕ) (tag : GateTag) (n p r : ℕ) (stream : BitString) :
    (body tag).Executes g (store n p r stream)
      (store n (p+1) r ((GateEmitter.chunk tag p).reverse++stream)) (14*p+71) := by
  have h₀ : (atom tag).Executes g (store n p r stream)
      (store n p r ((GateEmitter.chunk tag p).reverse++stream)) (14*p+68) := by
    apply rename_executes_to _ atomEmbedding g (GateEmitter.atom_executes g tag p stream)
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | (exfalso;exact hi 1 rfl)
  have h₁ : (push (1 : Fin 6) true).Executes g
      (store n p r ((GateEmitter.chunk tag p).reverse++stream))
      (store n (p+1) r ((GateEmitter.chunk tag p).reverse++stream)) 1 := by
    convert push_executes g (1 : Fin 6) true (store n p r ((GateEmitter.chunk tag p).reverse++stream)) using 1
    funext i;fin_cases i <;> simp [store,List.replicate_succ]
  convert seq_executes _ _ g h₀ h₁ using 1 <;> omega

lemma loop_execution (g : BitString → ℕ) (tag : GateTag) (n p r : ℕ) (stream : BitString) :
    ∃ c, WhileExecution (2 : Fin 6) (body tag) (body tag) g (store n p r stream)
      (store n (p+r) 0 ((chunks tag p r).reverse++stream)) c ∧ c≤r*(14*(p+r)+73)+1 := by
  induction r generalizing p stream with
  | zero => exact ⟨1,by simpa [chunks] using WhileExecution.empty (store n p 0 stream) rfl,by simp⟩
  | succ r ih =>
    have hb := body_executes g tag n p r stream
    have hu : Function.update (store n p (r+1) stream) (2 : Fin 6) (List.replicate r true)=store n p r stream := by
      funext i;fin_cases i <;> rfl
    obtain ⟨c,hc,hcb⟩ := ih (p+1) ((GateEmitter.chunk tag p).reverse++stream)
    have he := WhileExecution.one (stack := (2 : Fin 6)) (B := body tag) (C := body tag) (g := g)
      (show store n p (r+1) stream 2=true::List.replicate r true from rfl)
      (by rw [hu];exact hb) hc
    refine ⟨1+(14*p+71)+1+c,?_,?_⟩
    · simpa [chunks,List.range'_succ,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he
    · nlinarith

noncomputable def program (tag : GateTag) : OracleBlock 5 :=
  seq (copyOn 0 2 4 (by decide) (by decide) (by decide)) (seq (loop tag) (clear 1))

theorem program_executes (g : BitString → ℕ) (tag : GateTag) (n : ℕ) (stream : BitString) :
    ∃ c, (program tag).Executes g (store n 0 0 stream)
      (store n 0 0 ((chunks tag 0 n).reverse++stream)) c ∧ c≤14*n^2+79*n+8 := by
  have h₀ : (copyOn (0 : Fin 6) 2 4 (by decide) (by decide) (by decide)).Executes g
      (store n 0 0 stream) (store n 0 n stream) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 6) 2 4 (by decide) (by decide) (by decide) (store n 0 0 stream) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  obtain ⟨l,hl,hlb⟩ := loop_execution g tag n 0 n stream
  have h₁ : (loop tag).Executes g (store n 0 n stream) (store n n 0 ((chunks tag 0 n).reverse++stream)) l := by
    simpa using whilePop_executes _ _ _ g hl
  have h₂ : (clear (1 : Fin 6)).Executes g (store n n 0 ((chunks tag 0 n).reverse++stream))
      (store n 0 0 ((chunks tag 0 n).reverse++stream)) (n+1) := by
    convert clear_executes g (1 : Fin 6) (store n n 0 ((chunks tag 0 n).reverse++stream)) using 1
    · funext i;fin_cases i <;> rfl
    · simp [store]
  refine ⟨_,seq_executes _ _ g h₀ (seq_executes _ _ g h₁ h₂),?_⟩
  nlinarith

lemma program_queryFree (tag : GateTag) : (program tag).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _
    (whilePop_queryFree _ _ _ (seq_queryFree _ _ (rename_queryFree _ _ (GateEmitter.atom_queryFree tag)) (push_queryFree _ _))
      (seq_queryFree _ _ (rename_queryFree _ _ (GateEmitter.atom_queryFree tag)) (push_queryFree _ _))) (clear_queryFree _))

end HiddenCircuits.Circuit.Runtime.UniformGateEmitter
