import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! The first actual verifier stage parses both the certificate pair and the graph pair. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def outerParseEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun z : Fin 8 => z.val) h)
def innerParseEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 4 else if i.val=1 then 6 else if i.val=2 then 5 else 7
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def twoParseBlock : OracleBlock 7 :=
  seq (unpairOn outerParseEmbedding)
    (seq (copyOn 1 4 5 (by decide) (by decide) (by decide)) (unpairOn innerParseEmbedding))

def parse8Store (a b c d e f g h : BitString) : Store 7 := fun i =>
  if i.val=0 then a else if i.val=1 then b else if i.val=2 then c else if i.val=3 then d
  else if i.val=4 then e else if i.val=5 then f else if i.val=6 then g else h

def twoParseResult (xs : BitString) : Store 7 :=
  let r := parse xs
  let q := parse r.left
  parse8Store r.right r.left [] [r.ok] q.right [] q.left [q.ok]

def twoParseCost (xs : BitString) : ℕ :=
  (parseCost xs+2*(parse xs).left.length+1)+(5*(parse xs).left.length+2)+
    (parseCost (parse xs).left+2*(parse (parse xs).left).left.length+1)+4

theorem twoParse_executes (g : BitString → ℕ) (xs : BitString) :
    twoParseBlock.Executes g (Function.update (fun _ : Fin 8 => ([]:BitString)) 0 xs)
      (twoParseResult xs) (twoParseCost xs) := by
  let r := parse xs
  let q := parse r.left
  let s₀ : Store 7 := parse8Store xs [] [] [] [] [] [] []
  let s₁ : Store 7 := parse8Store r.right r.left [] [r.ok] [] [] [] []
  let s₂ : Store 7 := parse8Store r.right r.left [] [r.ok] r.left [] [] []
  have h₁ : (unpairOn outerParseEmbedding).Executes g s₀ s₁
      (parseCost xs+2*r.left.length+1) := by
    apply unpairOn_executes outerParseEmbedding g s₀ s₁ xs
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl)
  have h₂ : (copyOn (1:Fin 8) 4 5 (by decide) (by decide) (by decide)).Executes g s₁ s₂
      (5*r.left.length+2) := by
    have hh := copyOn_executes g (1:Fin 8) 4 5 (by decide) (by decide) (by decide) s₁ rfl
    have he : Function.update s₁ (4:Fin 8) (s₁ 1++s₁ 4)=s₂ := by
      funext i;fin_cases i <;> simp [s₁,s₂,parse8Store]
    rw [he] at hh
    exact hh
  have h₃ : (unpairOn innerParseEmbedding).Executes g s₂ (twoParseResult xs)
      (parseCost r.left+2*q.left.length+1) := by
    apply unpairOn_executes innerParseEmbedding g s₂ (twoParseResult xs) r.left
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro j hj
      fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl)
  have h := seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃)
  have he : Function.update (fun _ : Fin 8 => ([]:BitString)) 0 xs=s₀ := by
    funext i;fin_cases i <;> rfl
  rw [he]
  dsimp only [r,q] at h
  simpa only [twoParseCost,Nat.add_assoc] using h

 theorem parse_lengths (xs : BitString) : (parse xs).left.length ≤ xs.length ∧
    (parse xs).right.length ≤ xs.length := by
  cases xs with
  | nil => simp [parse]
  | cons b xs =>
    cases b with
    | false => simp [parse]
    | true =>
      cases xs with
      | nil => simp [parse]
      | cons b xs =>
        have ih := parse_lengths xs
        simp only [parse,List.length_cons]
        omega
termination_by xs.length

 theorem twoParse_cost_bound (xs : BitString) : twoParseCost xs ≤ 11*xs.length+14 := by
  have h₁ := unpair_cost_bound xs
  have h₂ := unpair_cost_bound (parse xs).left
  have h₃ := (parse_lengths xs).1
  unfold twoParseCost
  omega

 theorem twoParse_queryFree : twoParseBlock.QueryFree :=
  seq_queryFree _ _ (unpairOn_queryFree _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (unpairOn_queryFree _))

end HiddenCircuits.Complexity.GraphVerifier.Runtime
