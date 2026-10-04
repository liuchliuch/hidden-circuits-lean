import HiddenCircuits.Complexity.UnaryPolynomial
import HiddenCircuits.Complexity.CompilerSize

/-! Actual preparation of all polynomially bounded dimensions for a fixed #P
verifier. The original binary input is preserved, its unary length is obtained by
physical scanning, and every subsequent dimension is evaluated by real code. -/
namespace HiddenCircuits.Complexity.VerifierSetup
open OracleBlock Polynomial

inductive Dimension | witnesses | steps | height | cells | variables
  deriving DecidableEq

def slot : Dimension → Fin 18
  | .witnesses => 13
  | .steps => 8
  | .height => 9
  | .cells => 10
  | .variables => 14

def embedding (d : Dimension) : Fin 5 ↪ Fin 18 where
  toFun := Fin.cases 12 (Fin.cases (slot d) (Fin.cases 0 (Fin.cases 2 (fun _ => 3))))
  inj' := by cases d <;> decide

@[simp] lemma embedding_one (d : Dimension) : embedding d 1 = slot d := rfl

noncomputable def dimensionBlock (d : Dimension) (p : Polynomial ℕ) : OracleBlock 17 :=
  rename (UnaryPolynomial.polynomialBlock p) (embedding d)

def state (x : BitString) (m t height cells varCount : ℕ) : Store 17 := fun i =>
  if i.val=11 then x else List.replicate
    (if i.val=12 then x.length else if i.val=13 then m else if i.val=8 then t
      else if i.val=9 then height else if i.val=10 then cells else if i.val=14 then varCount else 0) true

noncomputable def seed : OracleBlock 17 :=
  seq (copyOn 0 11 4 (by decide) (by decide) (by decide)) (repeatPrepend 0 12 [true])

/-- Preserve the input and count its length by one real scan of a copied word. -/
theorem seed_executes (g : BitString → ℕ) (x : BitString) :
    seed.Executes g (Function.update (fun _ => []) 0 x) (state x 0 0 0 0 0) (11*x.length+5) := by
  let s : Store 17 := Function.update (fun _ => []) 0 x
  have hc := copyOn_executes g (0 : Fin 18) 11 4 (by decide) (by decide) (by decide) s rfl
  let s' := Function.update s 11 (s 0++s 11)
  have hr := repeatPrepend_executes g (0 : Fin 18) 12 (by decide) [true] s'
  have h := seq_executes _ _ g hc hr
  convert h using 1
  · funext i;fin_cases i <;> simp [state,s',s]
  · simp [s',s];ring

lemma seed_queryFree : seed.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (repeatPrepend_queryFree _ _ _)

noncomputable def variablesPolynomial {v : BitString → Bool}
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v) (p : Polynomial ℕ) : Polynomial ℕ :=
  p+(VerifierTableau.horizonPolynomial M p+1)*VerifierTableau.cellsPolynomial M p

noncomputable def polynomial {v : BitString → Bool}
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v) (p : Polynomial ℕ) : Dimension → Polynomial ℕ
  | .witnesses => p
  | .steps => VerifierTableau.horizonPolynomial M p
  | .height => VerifierTableau.heightPolynomial M p
  | .cells => VerifierTableau.cellsPolynomial M p
  | .variables => variablesPolynomial M p

variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v) (p : Polynomial ℕ)

noncomputable def program : OracleBlock 17 :=
  seq seed (seq (dimensionBlock .witnesses p)
    (seq (dimensionBlock .steps (polynomial M p .steps))
      (seq (dimensionBlock .height (polynomial M p .height))
        (seq (dimensionBlock .cells (polynomial M p .cells)) (dimensionBlock .variables (polynomial M p .variables))))))

noncomputable def time : Polynomial ℕ :=
  11*X+15+UnaryPolynomial.polynomialTime p+UnaryPolynomial.polynomialTime (polynomial M p .steps)+
    UnaryPolynomial.polynomialTime (polynomial M p .height)+UnaryPolynomial.polynomialTime (polynomial M p .cells)+
    UnaryPolynomial.polynomialTime (polynomial M p .variables)

/-- All five actual dimensions are produced by one fixed finite program, with an
explicit polynomial instruction bound in the original binary input length. -/
theorem program_executes (g : BitString → ℕ) (x : BitString) :
    (program M p).Executes g (Function.update (fun _ => []) 0 x)
      (state x (p.eval x.length) ((polynomial M p .steps).eval x.length)
        ((polynomial M p .height).eval x.length) ((polynomial M p .cells).eval x.length)
        ((polynomial M p .variables).eval x.length)) ((time M p).eval x.length) := by
  let n := x.length
  let m := p.eval n
  let t := (polynomial M p .steps).eval n
  let h := (polynomial M p .height).eval n
  let c := (polynomial M p .cells).eval n
  let vv := (polynomial M p .variables).eval n
  have hw : (dimensionBlock .witnesses p).Executes g (state x 0 0 0 0 0) (state x m 0 0 0 0)
      ((UnaryPolynomial.polynomialTime p).eval n) := by
    have hh : (state x 0 0 0 0 0) ∘ embedding .witnesses = UnaryPolynomial.state n 0 0 0 0 := by
      funext i;fin_cases i <;> rfl
    have he := UnaryPolynomial.polynomialOn_executes (embedding .witnesses) g p n (state x 0 0 0 0 0) hh
    convert he using 1
    funext i;fin_cases i <;> simp [state,slot,m]
  have ht : (dimensionBlock .steps (polynomial M p .steps)).Executes g (state x m 0 0 0 0) (state x m t 0 0 0)
      ((UnaryPolynomial.polynomialTime (polynomial M p .steps)).eval n) := by
    have hh : (state x m 0 0 0 0) ∘ embedding .steps = UnaryPolynomial.state n 0 0 0 0 := by
      funext i;fin_cases i <;> rfl
    have he := UnaryPolynomial.polynomialOn_executes (embedding .steps) g (polynomial M p .steps) n (state x m 0 0 0 0) hh
    convert he using 1
    funext i;fin_cases i <;> simp [state,slot,t]
  have hH : (dimensionBlock .height (polynomial M p .height)).Executes g (state x m t 0 0 0) (state x m t h 0 0)
      ((UnaryPolynomial.polynomialTime (polynomial M p .height)).eval n) := by
    have hh : (state x m t 0 0 0) ∘ embedding .height = UnaryPolynomial.state n 0 0 0 0 := by
      funext i;fin_cases i <;> rfl
    have he := UnaryPolynomial.polynomialOn_executes (embedding .height) g (polynomial M p .height) n (state x m t 0 0 0) hh
    convert he using 1
    funext i;fin_cases i <;> simp [state,slot,h]
  have hC : (dimensionBlock .cells (polynomial M p .cells)).Executes g (state x m t h 0 0) (state x m t h c 0)
      ((UnaryPolynomial.polynomialTime (polynomial M p .cells)).eval n) := by
    have hh : (state x m t h 0 0) ∘ embedding .cells = UnaryPolynomial.state n 0 0 0 0 := by
      funext i;fin_cases i <;> rfl
    have he := UnaryPolynomial.polynomialOn_executes (embedding .cells) g (polynomial M p .cells) n (state x m t h 0 0) hh
    convert he using 1
    funext i;fin_cases i <;> simp [state,slot,c]
  have hV : (dimensionBlock .variables (polynomial M p .variables)).Executes g (state x m t h c 0) (state x m t h c vv)
      ((UnaryPolynomial.polynomialTime (polynomial M p .variables)).eval n) := by
    have hh : (state x m t h c 0) ∘ embedding .variables = UnaryPolynomial.state n 0 0 0 0 := by
      funext i;fin_cases i <;> rfl
    have he := UnaryPolynomial.polynomialOn_executes (embedding .variables) g (polynomial M p .variables) n (state x m t h c 0) hh
    convert he using 1
    funext i;fin_cases i <;> simp [state,slot,vv]
  have he := seq_executes _ _ g (seed_executes g x)
    (seq_executes _ _ g hw (seq_executes _ _ g ht (seq_executes _ _ g hH (seq_executes _ _ g hC hV))))
  convert he using 1
  simp [time,n];ring

lemma program_queryFree : (program M p).QueryFree := by
  have hd (d : Dimension) (q : Polynomial ℕ) : (dimensionBlock d q).QueryFree :=
    rename_queryFree _ _ (UnaryPolynomial.polynomialBlock_queryFree q)
  exact seq_queryFree _ _ seed_queryFree (seq_queryFree _ _ (hd _ _)
    (seq_queryFree _ _ (hd _ _) (seq_queryFree _ _ (hd _ _) (seq_queryFree _ _ (hd _ _) (hd _ _)))))

end HiddenCircuits.Complexity.VerifierSetup
