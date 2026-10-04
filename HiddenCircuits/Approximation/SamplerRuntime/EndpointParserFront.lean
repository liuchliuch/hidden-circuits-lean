import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserFinish
import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserValidity
import HiddenCircuits.Complexity.GraphVerifier.HeaderStage

namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
open Complexity OracleBlock GraphVerifier.Runtime
set_option maxHeartbeats 800000

def input (xs : BitString) : Store 35 := fun i => if i.val=0 then xs else []
def copied (xs : BitString) : Store 35 := Function.update (input xs) 7 xs

def tripleMap : Fin 8 ↪ Fin 36 where
  toFun i := ![7,1,2,3,8,9,10,11] i
  inj' := by decide +kernel
def headerMap : Fin 4 ↪ Fin 36 where
  toFun i := ![1,12,8,13] i
  inj' := by decide +kernel

def parsed (xs : BitString) : Store 35 := fun i =>
  if i.val=0 then xs else if i.val=1 then (first xs).left else if i.val=2 then (second xs).left
  else if i.val=3 then (third xs).left else if i.val=7 then (third xs).right
  else if i.val=9 then [(first xs).ok] else if i.val=10 then [(second xs).ok]
  else if i.val=11 then [(third xs).ok] else []
def headered (xs : BitString) : Store 35 := Function.update (Function.update (parsed xs) 12
  (List.replicate (first xs).left.length true)) 13 [(first xs).left.all id]
def emptied (xs : BitString) : Store 35 := Function.update (Function.update (headered xs) 7 []) 8 [(third xs).right.isEmpty]
def prepared (xs : BitString) : Store 35 := fun i =>
  if i.val=0 then xs else if i.val=1 then (first xs).left else if i.val=2 then (second xs).left
  else if i.val=3 then (third xs).left else if i.val=12 then List.replicate (first xs).left.length true
  else if i.val=14 then [(initial xs).valid] else []
def frontConjunction : List Bool → Bool
  | [a,b,c,d,e] => a&&b&&c&&d&&e
  | _ => false
noncomputable def front : OracleBlock 35 := seq (copyOn 0 7 8 (by decide) (by decide) (by decide))
  (seq (rename tripleBlock tripleMap) (seq (headerOn headerMap)
    (seq (emptyCheck 7 8) (decision 14 [9,10,11,13,8] frontConjunction))))

lemma copy_executes (g : BitString → ℕ) (xs : BitString) :
    (copyOn (0:Fin 36) 7 8 (by decide) (by decide) (by decide)).Executes g (input xs) (copied xs) (5*xs.length+2) := by
  simpa [input,copied] using copyOn_executes g (0:Fin 36) 7 8 (by decide) (by decide) (by decide) (input xs) rfl
lemma triple_framed (g : BitString → ℕ) (xs : BitString) :
    (rename tripleBlock tripleMap).Executes g (copied xs) (parsed xs) (tripleCost xs) := by
  apply rename_executes_to tripleBlock tripleMap g (outerS:=copied xs) (outerT:=parsed xs) (triple_executes g xs)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) |
      exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | exact False.elim (hi 5 rfl) |
      exact False.elim (hi 6 rfl) | exact False.elim (hi 7 rfl)
lemma header_framed (g : BitString → ℕ) (xs : BitString) :
    (headerOn headerMap).Executes g (parsed xs) (headered xs) (5*(first xs).left.length+3) := by
  exact headerOn_executes headerMap g (parsed xs) (first xs).left (by funext i;fin_cases i <;> rfl)
lemma decide_framed (g : BitString → ℕ) (xs : BitString) :
    (decision (14:Fin 36) [9,10,11,13,8] frontConjunction).Executes g (emptied xs) (prepared xs) 14 := by
  let vals : Fin 36 → Bool := fun i => if i.val=9 then (first xs).ok else if i.val=10 then (second xs).ok
    else if i.val=11 then (third xs).ok else if i.val=13 then (first xs).left.all id else (third xs).right.isEmpty
  have hh := decision_executes (14:Fin 36) [9,10,11,13,8] (by decide) (by decide) frontConjunction vals g (emptied xs)
    (by intro i hi;fin_cases i <;> simp_all [emptied,headered,parsed,vals])
  convert hh using 1
  clear hh
  funext i;fin_cases i <;> simp [prepared,emptied,headered,parsed,eraseStore,frontConjunction,vals,initial]

theorem front_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,front.Executes g (input xs) (prepared xs) c ∧ c≤30*xs.length+100 := by
  obtain ⟨a,ha,hab⟩ := emptyCheck_executes (7:Fin 36) 8 (by decide) g (headered xs) rfl
  change (emptyCheck (7:Fin 36) 8).Executes g (headered xs) (emptied xs) a at ha
  change a≤(third xs).right.length+6 at hab
  refine ⟨_,seq_executes _ _ g (copy_executes g xs) (seq_executes _ _ g (triple_framed g xs)
    (seq_executes _ _ g (header_framed g xs) (seq_executes _ _ g ha (decide_framed g xs)))),?_⟩
  have ht := triple_cost_bound xs
  have h1 := head_lengths xs
  have h2 := head_lengths (first xs).right
  have h3 := head_lengths (second xs).right
  change (first xs).left.length≤xs.length ∧ (first xs).right.length≤xs.length at h1
  change (second xs).left.length≤(first xs).right.length ∧ (second xs).right.length≤(first xs).right.length at h2
  change (third xs).left.length≤(second xs).right.length ∧ (third xs).right.length≤(second xs).right.length at h3
  omega
lemma front_queryFree : front.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ triple_queryFree) (seq_queryFree _ _ (headerOn_queryFree _)
    (seq_queryFree _ _ (emptyCheck_queryFree _ _) (decision_queryFree _ _ _))))
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
