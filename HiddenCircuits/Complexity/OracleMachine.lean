import HiddenCircuits.Complexity.SharpP

/-!
# Finite binary-stack oracle machines and charged computation

Every ordinary instruction touches at most one bit. An oracle instruction is
charged for the complete query and answer. Thus it cannot conceal exponential
query lengths, output lengths, or work on oracle answers behind a unit-cost call.
The finite instruction language has no arbitrary function on binary strings.
-/
namespace HiddenCircuits.Complexity

/-- `k` stackCount and `q` control labelCount, both finite. -/
inductive OracleInstr (k q : ℕ)
  | halt
  | jump (next : Fin q)
  | push (stack : Fin k) (bit : Bool) (next : Fin q)
  | pop (stack : Fin k) (empty zero one : Fin q)
  | query (input output : Fin k) (next : Fin q)
  deriving DecidableEq

structure OracleConfig (k q : ℕ) where
  pc : Fin q
  stack : Fin k → BitString

/-- A genuinely finite program over binary stackCount. -/
structure OracleMachine where
  stackCount : ℕ
  labelCount : ℕ
  input : Fin stackCount
  output : Fin stackCount
  start : Fin labelCount
  code : Fin labelCount → OracleInstr stackCount labelCount

namespace OracleMachine
variable (M : OracleMachine)
abbrev Config := OracleConfig M.stackCount M.labelCount

/-- Query answers use the ordinary binary natural-number encoding. -/
def answerBits (g : BitString → ℕ) (x : BitString) : BitString :=
  Computability.encodeNat (g x)

def init (x : BitString) : M.Config :=
  ⟨M.start, Function.update (fun _ => []) M.input x⟩

/-- One instruction and its exact bit-operation charge. -/
def step (g : BitString → ℕ) (c : M.Config) : Option (M.Config × ℕ) :=
  match M.code c.pc with
  | .halt => none
  | .jump next => some (⟨next,c.stack⟩,1)
  | .push s b next => some (⟨next, Function.update c.stack s (b :: c.stack s)⟩, 1)
  | .pop s empty zero one =>
    match c.stack s with
    | [] => some (⟨empty,c.stack⟩,1)
    | b :: bs => some (⟨if b then one else zero,Function.update c.stack s bs⟩,1)
  | .query i o next =>
    let a := answerBits g (c.stack i)
    some (⟨next,Function.update c.stack o a⟩,1 + (c.stack i).length + a.length)

/-- An execution derivation contains every actual instruction. -/
inductive Runs (g : BitString → ℕ) : M.Config → M.Config → ℕ → Prop
  | halt (c) (h : M.step g c = none) : Runs g c c 0
  | next {c d e a b} (h : M.step g c = some (d,a)) (tail : Runs g d e b) :
      Runs g c e (a+b)

theorem step_cost_positive {g : BitString → ℕ} {c d : M.Config} {a : ℕ}
    (h : M.step g c = some (d,a)) : 0 < a := by
  unfold step at h
  split at h
  · contradiction
  · cases h; omega
  · cases h; omega
  · split at h <;> cases h <;> omega
  · cases h; omega

/-- A single step can grow any stack by no more than its charged cost. -/
theorem step_stack_bound {g : BitString → ℕ} {c d : M.Config} {a n : ℕ}
    (h : M.step g c = some (d,a)) (hc : ∀ s, (c.stack s).length ≤ n) :
    ∀ s, (d.stack s).length ≤ n + a := by
  cases hi : M.code c.pc with
  | halt => simp [step, hi] at h
  | jump next =>
    simp only [step,hi] at h
    cases h
    exact fun s => (hc s).trans (Nat.le_add_right _ 1)
  | push i b next =>
    simp only [step,hi] at h
    cases h
    intro s
    have hs := hc s
    have hi := hc i
    by_cases he : s = i
    · subst s; simpa using Nat.add_le_add_right hi 1
    · simp [Function.update_of_ne he, hs.trans (Nat.le_add_right _ 1)]
  | pop i empty zero one =>
    cases he : c.stack i with
    | nil =>
      simp only [step,hi,he] at h
      cases h
      intro s
      exact (hc s).trans (Nat.le_add_right _ 1)
    | cons b bs =>
      simp only [step,hi,he] at h
      cases h
      intro s
      have hs := hc s
      have hi := hc i
      rw [he] at hi
      by_cases hsi : s = i
      · subst s; simp only [Function.update_self]; simp only [List.length_cons] at hi; omega
      · simp only [Function.update_of_ne hsi]; omega
  | query i o next =>
    simp only [step,hi] at h
    cases h
    intro s
    have hs := hc s
    by_cases hso : s = o
    · subst s; simp only [Function.update_self]; omega
    · simp only [Function.update_of_ne hso]; omega

/-- The operational cost bounds all intermediate bit-string storage, including
oracle outputs. No separate query-size assumption is hidden in a reduction. -/
theorem Runs.stack_bound {g : BitString → ℕ} {c d : M.Config} {t n : ℕ}
    (h : M.Runs g c d t) (hc : ∀ s, (c.stack s).length ≤ n) :
    ∀ s, (d.stack s).length ≤ n + t := by
  induction h generalizing n with
  | halt c h => simpa using hc
  | next h tail ih =>
    have hd := M.step_stack_bound h hc
    simpa [Nat.add_assoc] using ih hd

theorem init_stack_bound (x : BitString) :
    ∀ s, ((M.init x).stack s).length ≤ x.length := by
  intro s
  simp only [init, Function.update_apply]
  split_ifs <;> simp

/-- The input plus charged time bounds the final output length. -/
theorem output_length_bound {g : BitString → ℕ} {x : BitString} {d : M.Config} {t : ℕ}
    (h : M.Runs g (M.init x) d t) :
    (d.stack M.output).length ≤ x.length + t :=
  Runs.stack_bound M h (M.init_stack_bound x) M.output

end OracleMachine

/-- Polynomial-time Turing counting reduction with actual finite programs,
actual executions, exact binary output, and a polynomial bit-operation bound. -/
def PolyTuringReduction (f g : BitString → ℕ) : Prop :=
  ∃ (M : OracleMachine) (p : Polynomial ℕ), ∀ x,
    ∃ (c : M.Config) (t : ℕ), M.Runs g (M.init x) c t ∧
      c.stack M.output = Computability.encodeNat (f x) ∧ t ≤ p.eval x.length

/-- The one-query identity oracle program. -/
def identityOracle : OracleMachine where
  stackCount := 1
  labelCount := 2
  input := 0
  output := 0
  start := 0
  code pc := if pc = 0 then .query 0 0 1 else .halt

/-- Reflexivity is proved for polynomial-output oracles. Charging the answer
length deliberately rules out unit-cost access to exponentially long strings. -/
theorem polyTuringReduction_refl {g : BitString → ℕ}
    (hg : ∃ p : Polynomial ℕ, ∀ x,
      (Computability.encodeNat (g x)).length ≤ p.eval x.length) :
    PolyTuringReduction g g := by
  obtain ⟨p,hp⟩ := hg
  refine ⟨identityOracle,Polynomial.X+p+1,fun x => ?_⟩
  let c : identityOracle.Config :=
    ⟨⟨1,by decide⟩,Function.update (identityOracle.init x).stack ⟨0,by decide⟩
      (Computability.encodeNat (g x))⟩
  refine ⟨c,1+x.length+(Computability.encodeNat (g x)).length,?_,?_,?_⟩
  · apply OracleMachine.Runs.next (a := 1+x.length+(Computability.encodeNat (g x)).length)
      (b := 0) (d := c)
    · simp [OracleMachine.step,identityOracle,OracleMachine.init,OracleMachine.answerBits,c]
    · apply OracleMachine.Runs.halt
      rfl
  · simp [c,identityOracle]
  · simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      (show 1+x.length+(Computability.encodeNat (g x)).length ≤ x.length+p.eval x.length+1 by
        have := hp x
        omega)

theorem SharpP.reduces_to_self {g : BitString → ℕ} (hg : SharpP g) :
    PolyTuringReduction g g := polyTuringReduction_refl hg.binary_output_bound

def SharpPHard (g : BitString → ℕ) : Prop :=
  ∀ f, SharpP f → PolyTuringReduction f g

def SharpPComplete (g : BitString → ℕ) : Prop :=
  SharpP g ∧ SharpPHard g

end HiddenCircuits.Complexity
