import HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
import HiddenCircuits.Complexity.OracleStream
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime

/-! Kernel-checked straight-line compilation over the previously constructed
bit-level integer operations. Safety refers only to mathematical divisibility
and bit bounds, and never supplies an execution or complexity assertion. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
open OracleBlock Polynomial

structure Instruction where
  op : Operation
  dest : Fin 7
  left : Fin 7
  right : Fin 7

def Instruction.eval (c : Instruction) (R : Fin 7 → ℤ) : Fin 7 → ℤ :=
  Function.update R c.dest (c.op.eval (R c.left) (R c.right))
noncomputable def Instruction.program (c : Instruction) : OracleBlock 15 :=
  assign c.op c.dest c.left c.right

def evaluate : List Instruction → (Fin 7 → ℤ) → (Fin 7 → ℤ)
  | [],R => R
  | c::cs,R => evaluate cs (c.eval R)

noncomputable def compile (cs : List Instruction) : OracleBlock 15 := sequence (cs.map Instruction.program)

def Bounded (B : ℕ) (R : Fin 7 → ℤ) : Prop := ∀ i, (signedBits (R i)).length ≤ B

def Safe (B : ℕ) : List Instruction → (Fin 7 → ℤ) → Prop
  | [],R => Bounded B R
  | c::cs,R => Bounded B R ∧ c.op.Valid (R c.left) (R c.right) ∧ Safe B cs (c.eval R)

lemma Safe.bounded {B : ℕ} {cs : List Instruction} {R : Fin 7 → ℤ} (h : Safe B cs R) : Bounded B R := by
  cases cs with
  | nil => exact h
  | cons c cs => exact h.1

theorem Safe.final {B : ℕ} {cs : List Instruction} {R : Fin 7 → ℤ} (h : Safe B cs R) :
    Bounded B (evaluate cs R) := by
  induction cs generalizing R with
  | nil => exact h
  | cons c cs ih => exact ih h.2.2

noncomputable def instructionTime : Polynomial ℕ := operationTime.comp (2*X)+17*X+20

theorem Instruction.executes (c : Instruction) (g : BitString → ℕ) (R : Fin 7 → ℤ) (B : ℕ)
    (hv : c.op.Valid (R c.left) (R c.right)) (hR : Bounded B R) (hS : Bounded B (c.eval R)) :
    ∃ t, c.program.Executes g (store [] [] (signedBits ∘ R))
      (store [] [] (signedBits ∘ c.eval R)) t ∧ t+2 ≤ instructionTime.eval B := by
  obtain ⟨t,ht,hb⟩ := assign_executes g c.op c.dest c.left c.right R hv
  refine ⟨t,ht,?_⟩
  have hi := hR c.left
  have hj := hR c.right
  have hd := hR c.dest
  have ho : (signedBits (c.op.eval (R c.left) (R c.right))).length ≤ B := by
    simpa only [Instruction.eval,Function.update_self] using hS c.dest
  have hm := polynomial_nat_eval_mono operationTime (show (signedBits (R c.left)).length+
      (signedBits (R c.right)).length ≤ 2*B by omega)
  dsimp only at hm
  simp only [instructionTime,eval_add,eval_mul,eval_comp,eval_ofNat,eval_X]
  omega

/-- The compiled fixed code list carries out every integer assignment using
actual binary-stack instructions and restores the nine work stacks each time. -/
theorem compile_executes (cs : List Instruction) (g : BitString → ℕ) (R : Fin 7 → ℤ) (B : ℕ)
    (h : Safe B cs R) :
    ∃ t, (compile cs).Executes g (store [] [] (signedBits ∘ R))
      (store [] [] (signedBits ∘ evaluate cs R)) t ∧
      t ≤ cs.length*instructionTime.eval B+1 := by
  induction cs generalizing R with
  | nil => exact ⟨1,skip_executes g _,by simp⟩
  | cons c cs ih =>
    obtain ⟨t,ht,hb⟩ := c.executes g R B h.2.1 h.1 h.2.2.bounded
    obtain ⟨u,hu,hub⟩ := ih (c.eval R) h.2.2
    refine ⟨t+u+2,seq_executes _ _ g ht hu,?_⟩
    simp only [List.length_cons,Nat.add_mul]
    omega

lemma compile_queryFree (cs : List Instruction) : (compile cs).QueryFree := by
  apply sequence_queryFree
  intro B hB
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hB
  exact assign_queryFree c.op c.dest c.left c.right

lemma operation_bitLength (op : Operation) (a b : ℤ) (B : ℕ)
    (ha : (signedBits a).length ≤ B) (hb : (signedBits b).length ≤ B) :
    (signedBits (op.eval a b)).length ≤ 2*B+3 := by
  have hA := abs_le_pow_signed_length a B ha
  have hB := abs_le_pow_signed_length b B hb
  cases op with
  | add =>
    have h := signedBits_length_of_abs_bound (add_abs_envelope B B a b hA hB)
    change (signedBits (a+b)).length ≤ _
    omega
  | multiply =>
    have hm : (a*b).natAbs ≤ 2^(B+B) := by
      simpa only [Int.natAbs_mul,pow_add] using Nat.mul_le_mul hA hB
    have h := signedBits_length_of_abs_bound hm
    change (signedBits (a*b)).length ≤ _
    omega
  | divide =>
    have hm := Nat.size_le_size (Int.natAbs_ediv_le_natAbs a b)
    change (signedBits (a/b)).length ≤ _
    simp only [signedBits,List.length_cons,encodeNat_length] at ha ⊢
    omega

lemma Bounded.mono {B C : ℕ} {R : Fin 7 → ℤ} (h : Bounded B R) (hBC : B≤C) : Bounded C R :=
  fun i => (h i).trans hBC

lemma Instruction.bounded (c : Instruction) (R : Fin 7 → ℤ) (B : ℕ) (h : Bounded B R) :
    Bounded (2*B+3) (c.eval R) := by
  intro i
  by_cases hi : i=c.dest
  · subst i
    simpa only [Instruction.eval,Function.update_self] using operation_bitLength c.op _ _ B (h c.left) (h c.right)
  · simp only [Instruction.eval,Function.update_of_ne hi]
    have := h i
    omega

/-- Only actual mathematical nonzero/exact-divisibility preconditions. -/
def Valid : List Instruction → (Fin 7 → ℤ) → Prop
  | [],_ => True
  | c::cs,R => c.op.Valid (R c.left) (R c.right) ∧ Valid cs (c.eval R)

theorem safe_of_bounded (cs : List Instruction) (R : Fin 7 → ℤ) (B : ℕ)
    (hb : Bounded B R) (hv : Valid cs R) : Safe (2^cs.length*(B+3)) cs R := by
  induction cs generalizing R B with
  | nil => exact hb.mono (by simp)
  | cons c cs ih =>
    have ht := ih (c.eval R) (2*B+3) (c.bounded R B hb) hv.2
    have he : 2^cs.length*(2*B+3+3)=2^(c::cs).length*(B+3) := by
      simp only [List.length_cons,pow_succ]
      ring
    rw [he] at ht
    refine ⟨hb.mono ?_,hv.1,ht⟩
    have hp : 1≤2^(c::cs).length := Nat.one_le_pow _ _ (by decide)
    nlinarith

noncomputable def straightTime (cs : List Instruction) : Polynomial ℕ :=
  C cs.length * instructionTime.comp (C (2^cs.length)*(X+3))+1

/-- A fixed straight-line arithmetic program has a genuine polynomial runtime
in the input register lengths. Every intermediate-size condition is discharged. -/
theorem compile_polynomial (cs : List Instruction) (g : BitString → ℕ) (R : Fin 7 → ℤ) (B : ℕ)
    (hb : Bounded B R) (hv : Valid cs R) :
    ∃ t, (compile cs).Executes g (store [] [] (signedBits ∘ R))
      (store [] [] (signedBits ∘ evaluate cs R)) t ∧ t ≤ (straightTime cs).eval B := by
  simpa only [straightTime,eval_add,eval_mul,eval_C,eval_comp,eval_X,eval_ofNat,eval_one] using
    compile_executes cs g R _ (safe_of_bounded cs R B hb hv)

end HiddenCircuits.Complexity.BinaryArithmetic.RegisterMachine
