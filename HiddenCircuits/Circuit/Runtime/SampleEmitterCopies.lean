import HiddenCircuits.Circuit.Runtime.SampleEmitterDelta

namespace HiddenCircuits.Circuit.Runtime.SampleEmitter
open HiddenCircuits.Complexity OracleBlock

def sampleIndex (second : Bool) : Fin 32 := if second then 2 else 1
def sampleNumber (second : Bool) (r s : ℕ) : ℕ := if second then s else r
noncomputable def copyIndex (second : Bool) : OracleBlock 31 :=
  copyOn (sampleIndex second) 13 17 (by cases second <;> decide) (by cases second <;> decide) (by decide)
noncomputable def doubleIndex (second : Bool) : OracleBlock 31 := seq (copyIndex second) (copyIndex second)
noncomputable def copies (second : Bool) : OracleBlock 31 := seq (doubleIndex second) repeatedSample

theorem copyIndex_executes (g : BitString → ℕ) (second : Bool) (circuit : BitString) (r s u n base clock : ℕ)
    (gates atom tag out exponent sign : BitString) :
    (copyIndex second).Executes g (store circuit r s u n base clock gates atom tag out exponent sign)
      (store circuit r s u n base (clock+sampleNumber second r s) gates atom tag out exponent sign)
      (5*sampleNumber second r s+2) := by
  have h := copyOn_executes g (sampleIndex second) (13:Fin 32) 17
    (by cases second <;> decide) (by cases second <;> decide) (by decide)
    (store circuit r s u n base clock gates atom tag out exponent sign) rfl
  convert h using 1
  · funext i;cases second <;> fin_cases i <;> simp [store,sampleIndex,sampleNumber,←List.replicate_add,Nat.add_comm]
  · cases second <;> simp [store,sampleIndex,sampleNumber]

theorem doubleIndex_executes (g : BitString → ℕ) (second : Bool) (circuit : BitString) (r s u n base : ℕ)
    (gates atom tag out exponent sign : BitString) :
    (doubleIndex second).Executes g (store circuit r s u n base 0 gates atom tag out exponent sign)
      (store circuit r s u n base (2*sampleNumber second r s) gates atom tag out exponent sign)
      (10*sampleNumber second r s+6) := by
  have h1 := copyIndex_executes g second circuit r s u n base 0 gates atom tag out exponent sign
  simp only [Nat.zero_add] at h1
  have h2 := copyIndex_executes g second circuit r s u n base (sampleNumber second r s) gates atom tag out exponent sign
  have h := seq_executes (copyIndex second) (copyIndex second) g h1 h2
  simpa only [←two_mul,show 2*(5*sampleNumber second r s+2)+2=10*sampleNumber second r s+6 by omega] using h

theorem copies_executes (g : BitString → ℕ) (second : Bool) {n : ℕ} (p : Placement n 2)
    (circuit : BitString) (r s u : ℕ) (gates atom tag out exponent sign : BitString) :
    ∃cost, (copies second).Executes g (store circuit r s u n (4*p.before) 0 gates atom tag out exponent sign)
      (store circuit r s u n (4*p.before) 0 gates atom tag
        (((List.replicate (2*sampleNumber second r s) (deltaBytes ((sampleGWord u).lift p))).flatten).reverse++out)
        (List.replicate (2*sampleNumber second r s*(290*u+372+SampleScalar.projectionExponent n)) true++exponent) sign) cost ∧
      cost≤2*sampleNumber second r s*(deltaTime n u+2)+10*sampleNumber second r s+9 := by
  have hd := doubleIndex_executes g second circuit r s u n (4*p.before) gates atom tag out exponent sign
  obtain ⟨cl,hl,hbl⟩ := repeatedSample_execution g p circuit r s u (2*sampleNumber second r s) gates atom tag out exponent sign
  refine ⟨_,seq_executes (doubleIndex second) repeatedSample g hd (whilePop_executes _ _ _ g hl),?_⟩
  omega

lemma copyIndex_queryFree (second : Bool) : (copyIndex second).QueryFree := copyOn_queryFree _ _ _ _ _ _
lemma doubleIndex_queryFree (second : Bool) : (doubleIndex second).QueryFree := seq_queryFree _ _ (copyIndex_queryFree _) (copyIndex_queryFree _)
lemma copies_queryFree (second : Bool) : (copies second).QueryFree := seq_queryFree _ _ (doubleIndex_queryFree _) repeatedSample_queryFree

end HiddenCircuits.Circuit.Runtime.SampleEmitter
