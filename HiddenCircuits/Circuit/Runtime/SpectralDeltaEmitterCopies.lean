import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterModel

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
open Complexity OracleBlock

theorem atom_executes (g : BitString → ℕ) (a : GateTag) (circuit : BitString) (r s n p : ℕ)
    (out stream tag clock left right result : BitString) :
    (atom a).Executes g (store circuit r s n out stream (List.replicate p true) tag clock left right result)
      (store circuit r s n ((GateEmitter.chunk a p).reverse++out) stream (List.replicate p true) tag clock left right result)
      (14*p+68) := by
  apply rename_executes_to _ gateMap g (GateEmitter.atom_executes g a p out)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    all_goals first | exact (hi 1 rfl).elim | rfl

def sampleNumber (second : Bool) (r s : ℕ) : ℕ := if second then s else r
def samplePort (second : Bool) : Fin 16 := if second then 2 else 1
noncomputable def copyIndex (second : Bool) : OracleBlock 15 :=
  copyOn (samplePort second) 9 14 (by cases second <;> decide) (by cases second <;> decide) (by decide)
noncomputable def repeated : OracleBlock 15 := whilePop 9 (atom .forbid) (atom .forbid)

theorem copyIndex_executes (g : BitString → ℕ) (second : Bool) (circuit : BitString) (r s n count : ℕ)
    (out stream position tag left right result : BitString) :
    (copyIndex second).Executes g (store circuit r s n out stream position tag (List.replicate count true) left right result)
      (store circuit r s n out stream position tag (List.replicate (count+sampleNumber second r s) true) left right result)
      (5*sampleNumber second r s+2) := by
  have h := copyOn_executes g (samplePort second) (9:Fin 16) 14
    (by cases second <;> decide) (by cases second <;> decide) (by decide)
    (store circuit r s n out stream position tag (List.replicate count true) left right result) rfl
  convert h using 1
  · funext i;cases second <;> fin_cases i <;> simp [store,samplePort,sampleNumber,←List.replicate_add,Nat.add_comm]
  · cases second <;> simp [store,samplePort,sampleNumber]

lemma pop_clock (circuit : BitString) (r s n count : ℕ) (out stream position tag left right result : BitString) :
    Function.update (store circuit r s n out stream position tag (List.replicate (count+1) true) left right result)
      9 (List.replicate count true)=store circuit r s n out stream position tag (List.replicate count true) left right result := by
  funext i;fin_cases i <;> rfl

theorem repeated_executes (g : BitString → ℕ) (circuit : BitString) (r s n p count : ℕ)
    (out stream tag left right result : BitString) :
    ∃ cost, WhileExecution (9:Fin 16) (atom .forbid) (atom .forbid) g
      (store circuit r s n out stream (List.replicate p true) tag (List.replicate count true) left right result)
      (store circuit r s n (((List.replicate count (GateEmitter.chunk .forbid p)).flatten).reverse++out)
        stream (List.replicate p true) tag [] left right result) cost ∧ cost ≤ count*(14*p+70)+1 := by
  induction count generalizing out with
  | zero => exact ⟨1,by simpa using WhileExecution.empty (store circuit r s n out stream (List.replicate p true) tag [] left right result) rfl,by simp⟩
  | succ count ih =>
    have ha := atom_executes g .forbid circuit r s n p out stream tag (List.replicate count true) left right result
    obtain ⟨ct,ht,hbt⟩ := ih ((GateEmitter.chunk .forbid p).reverse++out)
    rw [←pop_clock circuit r s n count out stream (List.replicate p true) tag left right result] at ha
    have h := WhileExecution.one (stack:=(9:Fin 16)) (B:=atom .forbid) (C:=atom .forbid) (g:=g) rfl ha ht
    refine ⟨1+(14*p+68)+1+ct,?_,?_⟩
    · convert h using 1
      simp only [List.replicate_succ,List.flatten_cons,List.reverse_append,List.append_assoc]
    · nlinarith

theorem copies_executes (g : BitString → ℕ) (second : Bool) (circuit : BitString) (r s n p : ℕ)
    (out stream tag left right result : BitString) :
    ∃ cost, (copies (samplePort second) (by cases second <;> decide) (by cases second <;> decide)).Executes g
      (store circuit r s n out stream (List.replicate p true) tag [] left right result)
      (store circuit r s n (((List.replicate (2*sampleNumber second r s) (GateEmitter.chunk .forbid p)).flatten).reverse++out)
        stream (List.replicate p true) tag [] left right result) cost ∧
      cost ≤ 2*sampleNumber second r s*(14*p+70)+10*sampleNumber second r s+9 := by
  have h1 := copyIndex_executes g second circuit r s n 0 out stream (List.replicate p true) tag left right result
  simp only [Nat.zero_add] at h1
  have h2 := copyIndex_executes g second circuit r s n (sampleNumber second r s) out stream (List.replicate p true) tag left right result
  rw [←two_mul] at h2
  obtain ⟨cl,hl,hbl⟩ := repeated_executes g circuit r s n p (2*sampleNumber second r s) out stream tag left right result
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (whilePop_executes _ _ _ g hl)),?_⟩
  omega

lemma atom_queryFree (a : GateTag) : (atom a).QueryFree := rename_queryFree _ _ (GateEmitter.atom_queryFree a)
lemma copies_queryFree (p : Fin 16) (h₁ : p≠9) (h₂ : p≠14) : (copies p h₁ h₂).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (whilePop_queryFree _ _ _ (atom_queryFree _) (atom_queryFree _)))
end HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
