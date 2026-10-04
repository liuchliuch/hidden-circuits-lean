import HiddenCircuits.Circuit.Runtime.BoundaryTransportEncoding

/-! A finite bit scanner emits only the X gates requested by the actual mask. -/
namespace HiddenCircuits.Circuit.Runtime.BoundaryTransport
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

def store (bits : BitString) (i : ℕ) (out : BitString) : Store 4 :=
  ![bits,List.replicate i true,out,[],[]]
def gateMap : Fin 4 ↪ Fin 5 where
  toFun i:=![1,2,3,4] i
  inj':=by decide +kernel
noncomputable def gate : OracleBlock 4 := rename (GateEmitter.atom .swap) gateMap
noncomputable def zero : OracleBlock 4 := push 1 true
noncomputable def one : OracleBlock 4 := seq gate zero
noncomputable def scan : OracleBlock 4 := whilePop 0 zero one
noncomputable def program : OracleBlock 4 := seq scan (clear 1)

lemma gate_executes (g : BitString→ℕ) (bits out : BitString) (i : ℕ) :
    gate.Executes g (store bits i out) (store bits i ((GateEmitter.chunk .swap i).reverse++out)) (14*i+68) := by
  apply rename_executes_to _ gateMap g (GateEmitter.atom_executes g .swap i out)
  · funext j;fin_cases j <;> rfl
  · funext j;fin_cases j <;> rfl
  · intro j hj;fin_cases j <;> first | rfl | (exfalso;exact hj 1 rfl)
lemma zero_executes (g : BitString→ℕ) (bits out : BitString) (i : ℕ) :
    zero.Executes g (store bits i out) (store bits (i+1) out) 1 := by
  convert push_executes g (1:Fin 5) true (store bits i out) using 1
  funext j;fin_cases j <;> simp [store,List.replicate_succ]
lemma one_executes (g : BitString→ℕ) (bits out : BitString) (i : ℕ) :
    one.Executes g (store bits i out) (store bits (i+1) ((GateEmitter.chunk .swap i).reverse++out)) (14*i+71) := by
  convert seq_executes _ _ g (gate_executes g bits out i)
    (zero_executes g bits ((GateEmitter.chunk .swap i).reverse++out) i) using 1 <;> omega

lemma scan_execution (g : BitString→ℕ) (bits : BitString) (i B : ℕ) (out : BitString)
    (hB : i+bits.length ≤ B) :
    ∃c,WhileExecution (0:Fin 5) zero one g (store bits i out)
      (store [] (i+bits.length) ((chunks bits i).reverse++out)) c ∧
      c ≤ bits.length*(14*B+73)+1 := by
  induction bits generalizing i out with
  | nil=>exact ⟨1,by simpa [chunks] using WhileExecution.empty (store [] i out) rfl,by simp⟩
  | cons b bs ih=>
    have hi : i+1+bs.length ≤ B := by simp only [List.length_cons] at hB;omega
    cases b with
    | false=>
      obtain ⟨c,hc,hb⟩:=ih (i+1) out hi
      have hu : Function.update (store (false::bs) i out) (0:Fin 5) bs=store bs i out := by
        funext j;fin_cases j <;> rfl
      have hh:=WhileExecution.zero (stack:=(0:Fin 5)) (B:=zero) (C:=one) (g:=g)
        (s:=store (false::bs) i out) (rest:=bs) rfl (by rw [hu];exact zero_executes g bs out i) hc
      refine ⟨1+1+1+c,?_,?_⟩
      · simpa only [chunks,Bool.false_eq_true,↓reduceIte,List.nil_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
      · simp only [List.length_cons];nlinarith
    | true=>
      obtain ⟨c,hc,hb⟩:=ih (i+1) ((GateEmitter.chunk .swap i).reverse++out) hi
      have hu : Function.update (store (true::bs) i out) (0:Fin 5) bs=store bs i out := by
        funext j;fin_cases j <;> rfl
      have hh:=WhileExecution.one (stack:=(0:Fin 5)) (B:=zero) (C:=one) (g:=g)
        (s:=store (true::bs) i out) (rest:=bs) rfl (by rw [hu];exact one_executes g bs out i) hc
      refine ⟨1+(14*i+71)+1+c,?_,?_⟩
      · simpa only [chunks,↓reduceIte,List.reverse_append,List.append_assoc,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
      · simp only [List.length_cons];nlinarith

lemma program_executes (g : BitString→ℕ) (bits out : BitString) :
    ∃c,program.Executes g (store bits 0 out) (store [] 0 ((chunks bits 0).reverse++out)) c ∧
      c ≤ bits.length*(14*bits.length+74)+4 := by
  obtain ⟨c,hc,hb⟩:=scan_execution g bits 0 bits.length out (by omega)
  have hs:=whilePop_executes _ _ _ g hc
  simp only [Nat.zero_add] at hs
  have he : (clear (1:Fin 5)).Executes g (store [] bits.length ((chunks bits 0).reverse++out))
      (store [] 0 ((chunks bits 0).reverse++out)) (bits.length+1) := by
    convert clear_executes g (1:Fin 5) (store [] bits.length ((chunks bits 0).reverse++out)) using 1
    · funext j;fin_cases j <;> rfl
    · simp [store]
  exact ⟨c+(bits.length+1)+2,seq_executes _ _ g hs he,by nlinarith⟩
lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (whilePop_queryFree _ _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ (GateEmitter.atom_queryFree _)) (push_queryFree _ _))) (clear_queryFree _)
noncomputable def on {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : OracleBlock k := rename program φ
lemma on_executes {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) (g : BitString→ℕ) (bits out : BitString)
    (s t : Store k) (hs : s∘φ=store bits 0 out) (ht : t∘φ=store [] 0 ((chunks bits 0).reverse++out))
    (hf : ∀j,(∀i,φ i≠j)→t j=s j) :
    ∃c,(on φ).Executes g s t c ∧ c ≤ bits.length*(14*bits.length+74)+4 := by
  obtain ⟨c,hc,hb⟩:=program_executes g bits out
  exact ⟨c,rename_executes_to _ φ g hc hs ht hf,hb⟩
lemma on_queryFree {k : ℕ} (φ : Fin 5 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.BoundaryTransport
