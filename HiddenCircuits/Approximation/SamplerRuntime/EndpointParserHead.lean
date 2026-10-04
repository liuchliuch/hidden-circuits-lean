import HiddenCircuits.GraphReduction.MonotoneEndpointEncoding
import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! Literal total extraction of one self-delimiting list field. Malformed list
markers produce a false flag, and every raw input has a linear execution bound. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime

def headResult : BitString → ParseResult
  | true::xs => parse xs
  | false::xs => ⟨[],xs,false⟩
  | [] => ⟨[],[],false⟩
noncomputable def headBlock : OracleBlock 3 := branchPop 0 (push 3 false) (push 3 false) unpairBlock

def headCost : BitString → ℕ
  | true::xs => parseCost xs+2*(parse xs).left.length+3
  | _ => 3

lemma flag_executes (g : BitString → ℕ) (xs : BitString) :
    (push (3:Fin 4) false).Executes g (parseStore xs [] [] []) (parseStore xs [] [] [false]) 1 := by
  convert push_executes g (3:Fin 4) false (parseStore xs [] [] []) using 1
  funext i;fin_cases i <;> rfl

theorem head_executes (g : BitString → ℕ) (xs : BitString) :
    headBlock.Executes g (parseStore xs [] [] [])
      (parseStore (headResult xs).right (headResult xs).left [] [(headResult xs).ok]) (headCost xs) := by
  cases xs with
  | nil =>
    exact branchPop_empty (0:Fin 4) (push 3 false) (push 3 false) unpairBlock g
      (s:=parseStore [] [] [] []) rfl (flag_executes g [])
  | cons b xs =>
    have hstore : Function.update (parseStore (b::xs) [] [] []) (0:Fin 4) xs=parseStore xs [] [] [] := by
      funext i;fin_cases i <;> rfl
    cases b
    · apply branchPop_false (0:Fin 4) (push 3 false) (push 3 false) unpairBlock g rfl
      rw [hstore]
      exact flag_executes g xs
    · have hp := unpairBlock_executes g xs
      simpa only [headBlock,headResult,headCost,hstore,Nat.add_assoc] using
        branchPop_true (0:Fin 4) (push 3 false) (push 3 false) unpairBlock g
          (s:=parseStore (true::xs) [] [] []) (rest:=xs) rfl (by rw [hstore];exact hp)

lemma head_queryFree : headBlock.QueryFree := branchPop_queryFree _ _ _ _
  (push_queryFree _ _) (push_queryFree _ _) unpairBlock_queryFree

theorem head_cost_bound (xs : BitString) : headCost xs ≤ 3*xs.length+6 := by
  cases xs with
  | nil => simp [headCost]
  | cons b xs =>
    cases b
    · simp [headCost]
    · have h := unpair_cost_bound xs
      simp only [headCost,List.length_cons]
      omega

@[simp] theorem headResult_word (word rest : BitString) : headResult (true::pairBits word rest)=⟨word,rest,true⟩ := by
  simp [headResult]

noncomputable def headOn {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : OracleBlock k := rename headBlock φ

theorem headOn_executes {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s t : Store k) (xs : BitString) (hs : s∘φ=parseStore xs [] [] [])
    (ht : t∘φ=parseStore (headResult xs).right (headResult xs).left [] [(headResult xs).ok])
    (hoff : ∀i,(∀j,φ j≠i)→s i=t i) :
    (headOn φ).Executes g s t (headCost xs) :=
  rename_executes_to headBlock φ g (head_executes g xs) hs ht (fun i hi => (hoff i hi).symm)
lemma headOn_queryFree {k : ℕ} (φ : Fin 4 ↪ Fin (k+1)) : (headOn φ).QueryFree := rename_queryFree _ _ head_queryFree
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
