import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserHead
import HiddenCircuits.Complexity.GraphVerifier.TwoParse

/-! Three real total list-field extractions for the endpoint input header and
two arrays. All raw inputs terminate with a linear bound and explicit flags. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime

lemma head_lengths (xs : BitString) : (headResult xs).left.length ≤ xs.length ∧
    (headResult xs).right.length ≤ xs.length := by
  cases xs with
  | nil => simp [headResult]
  | cons b xs =>
    cases b
    · simp [headResult]
    · have h := parse_lengths xs
      simp only [headResult,List.length_cons]
      exact ⟨by omega,by omega⟩

def tripleStore (rest a b c flag₁ flag₂ flag₃ : BitString) : Store 7 := fun i =>
  if i.val=0 then rest else if i.val=1 then a else if i.val=2 then b else if i.val=3 then c
  else if i.val=5 then flag₁ else if i.val=6 then flag₂ else if i.val=7 then flag₃ else []

def tripleEmbedding (q : Fin 3) : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 0 else if i.val=1 then ⟨q.val+1,by omega⟩
    else if i.val=2 then 4 else ⟨q.val+5,by omega⟩
  inj' := by fin_cases q <;> decide +kernel
noncomputable def tripleBlock : OracleBlock 7 := seq (headOn (tripleEmbedding 0))
  (seq (headOn (tripleEmbedding 1)) (headOn (tripleEmbedding 2)))

def first (xs : BitString) : ParseResult := headResult xs
def second (xs : BitString) : ParseResult := headResult (first xs).right
def third (xs : BitString) : ParseResult := headResult (second xs).right
def tripleResult (xs : BitString) : Store 7 := tripleStore (third xs).right (first xs).left (second xs).left (third xs).left
  [(first xs).ok] [(second xs).ok] [(third xs).ok]
def tripleCost (xs : BitString) : ℕ := headCost xs+headCost (first xs).right+headCost (second xs).right+4

theorem triple_executes (g : BitString → ℕ) (xs : BitString) :
    tripleBlock.Executes g (tripleStore xs [] [] [] [] [] []) (tripleResult xs) (tripleCost xs) := by
  let s₀ := tripleStore xs [] [] [] [] [] []
  let s₁ := tripleStore (first xs).right (first xs).left [] [] [(first xs).ok] [] []
  let s₂ := tripleStore (second xs).right (first xs).left (second xs).left [] [(first xs).ok] [(second xs).ok] []
  have h₁ : (headOn (tripleEmbedding 0)).Executes g s₀ s₁ (headCost xs) := by
    apply headOn_executes _ g s₀ s₁ xs
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim
  have h₂ : (headOn (tripleEmbedding 1)).Executes g s₁ s₂ (headCost (first xs).right) := by
    apply headOn_executes _ g s₁ s₂ (first xs).right
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim
  have h₃ : (headOn (tripleEmbedding 2)).Executes g s₂ (tripleResult xs) (headCost (second xs).right) := by
    apply headOn_executes _ g s₂ (tripleResult xs) (second xs).right
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 3 rfl).elim
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃) using 1 <;> simp only [tripleCost] <;> omega

lemma triple_queryFree : tripleBlock.QueryFree := seq_queryFree _ _ (headOn_queryFree _)
  (seq_queryFree _ _ (headOn_queryFree _) (headOn_queryFree _))

theorem triple_cost_bound (xs : BitString) : tripleCost xs ≤ 9*xs.length+22 := by
  have h₁ := head_cost_bound xs
  have h₂ := head_cost_bound (first xs).right
  have h₃ := head_cost_bound (second xs).right
  have l₁ : (first xs).right.length ≤ xs.length := (head_lengths xs).2
  have l₂ : (second xs).right.length ≤ (first xs).right.length := (head_lengths (first xs).right).2
  unfold tripleCost
  omega

@[simp] theorem tripleResult_encode (a b c : BitString) :
    tripleResult (encodeBitList [a,b,c])=tripleStore [] a b c [true] [true] [true] := by
  simp [tripleResult,first,second,third,encodeBitList,headResult]

lemma parse_reconstruct (xs : BitString) (h : (parse xs).ok=true) : pairBits (parse xs).left (parse xs).right=xs := by
  cases xs with
  | nil => simp [parse] at h
  | cons b xs =>
    cases b
    · rfl
    · cases xs with
      | nil => simp [parse] at h
      | cons b xs =>
        have ih := parse_reconstruct xs h
        simpa only [parse,pairBits,ih]
termination_by xs.length

lemma head_reconstruct (xs : BitString) (h : (headResult xs).ok=true) :
    xs=true::pairBits (headResult xs).left (headResult xs).right := by
  cases xs with
  | nil => simp [headResult] at h
  | cons b xs =>
    cases b
    · simp [headResult] at h
    · exact congrArg (List.cons true) (parse_reconstruct xs h).symm

theorem triple_decode (xs : BitString) (h₁ : (first xs).ok=true) (h₂ : (second xs).ok=true)
    (h₃ : (third xs).ok=true) (hr : (third xs).right=[]) :
    decodeBitList xs=some [(first xs).left,(second xs).left,(third xs).left] := by
  have a := head_reconstruct xs h₁
  have b := head_reconstruct (first xs).right h₂
  have c := head_reconstruct (second xs).right h₃
  change (first xs).right=true::pairBits (second xs).left (second xs).right at b
  change (second xs).right=true::pairBits (third xs).left (third xs).right at c
  have he : xs=encodeBitList [(first xs).left,(second xs).left,(third xs).left] := by
    calc
      xs = true::pairBits (first xs).left (first xs).right := a
      _ = true::pairBits (first xs).left (true::pairBits (second xs).left (true::pairBits (third xs).left [])) := by rw [b,c,hr]
      _ = _ := rfl
  exact (congrArg decodeBitList he).trans (decodeBitList_encode _)
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
