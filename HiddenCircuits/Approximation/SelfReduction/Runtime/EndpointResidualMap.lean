import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualScalar
import HiddenCircuits.Approximation.SelfReduction.Runtime.MapLoop
import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserHead

/-! A finite unary endpoint-array map. Each element is parsed, compared with
the runtime selected column, possibly popped once, and serialized in order. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
open Complexity OracleBlock SamplerRuntime.EndpointFiber
open GraphVerifier GraphVerifier.Runtime

def arrayStore (source chosen word output flag x y tmp : BitString) : Store 7 := fun i =>
  if i.val=0 then source else if i.val=1 then chosen else if i.val=2 then word else if i.val=3 then output
  else if i.val=4 then flag else if i.val=5 then x else if i.val=6 then y else tmp

def arrayParseMap : Fin 4 ↪ Fin 8 where
  toFun i := ![0,2,7,4] i
  inj' := by decide +kernel
def arrayScalarMap : Fin 6 ↪ Fin 8 where
  toFun i := ![1,2,4,5,6,7] i
  inj' := by decide +kernel
noncomputable def arrayParse : OracleBlock 7 := unpairOn arrayParseMap
noncomputable def arrayBody : OracleBlock 7 := seq arrayParse (seq (clear 4)
  (seq (scalarOn arrayScalarMap) (emitWordReversed 2 3)))
noncomputable def arrayLoop : OracleBlock 7 := whilePop 0 skip arrayBody
noncomputable def arrayMap : OracleBlock 7 := seq arrayLoop (reverseOn 3 0 (by decide))

def natWords (xs : List ℕ) : List BitString := xs.map unary
def natBits (xs : List ℕ) : BitString := encodeBitList (natWords xs)

lemma arrayParse_executes (g : BitString  →  ℕ) (j t : ℕ) (rest output : BitString) :
    arrayParse.Executes g (arrayStore (pairBits (unary t) rest) (unary j) [] output [] [] [] [])
      (arrayStore rest (unary j) (unary t) output [true] [] [] []) (5*t+3) := by
  have h := unpairOn_executes arrayParseMap g
    (arrayStore (pairBits (unary t) rest) (unary j) [] output [] [] [] [])
    (arrayStore rest (unary j) (unary t) output [true] [] [] []) (pairBits (unary t) rest)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [parse_pair] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim)
  convert h using 1
  simp [parse_pair,BinaryArithmetic.pair_parse_cost]
  omega

theorem arrayBody_executes (g : BitString  →  ℕ) (j t : ℕ) (rest output : BitString) :
    ∃cost, arrayBody.Executes g (arrayStore (pairBits (unary t) rest) (unary j) [] output [] [] [] [])
      (arrayStore rest (unary j) [] ((true::pairBits (unary (dropBoundary j t)) []).reverse++output) [] [] [] []) cost ∧
      cost+2 ≤ 24*t+13*j+48 := by
  have hp := arrayParse_executes g j t rest output
  have hc : (clear (4:Fin 8)).Executes g
      (arrayStore rest (unary j) (unary t) output [true] [] [] [])
      (arrayStore rest (unary j) (unary t) output [] [] [] []) 2 := by
    convert clear_executes g (4:Fin 8) (arrayStore rest (unary j) (unary t) output [true] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hs,hb⟩ := scalarOn_executes arrayScalarMap g
    (arrayStore rest (unary j) (unary t) output [] [] [] []) j t (by funext i;fin_cases i <;> rfl)
  have hs' : (scalarOn arrayScalarMap).Executes g
      (arrayStore rest (unary j) (unary t) output [] [] [] [])
      (arrayStore rest (unary j) (unary (dropBoundary j t)) output [] [] [] []) c := by
    convert hs using 1
    funext i;fin_cases i <;> rfl
  have he : (emitWordReversed (2:Fin 8) 3).Executes g
      (arrayStore rest (unary j) (unary (dropBoundary j t)) output [] [] [] [])
      (arrayStore rest (unary j) [] ((true::pairBits (unary (dropBoundary j t)) []).reverse++output) [] [] [] [])
      (6*dropBoundary j t+7) := by
    convert emitWordReversed_executes g (2:Fin 8) 3 (by decide)
      (arrayStore rest (unary j) (unary (dropBoundary j t)) output [] [] [] []) using 1
    · funext i;fin_cases i <;> rfl
    · simp [arrayStore]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hs' he)),?_⟩
  have hd : dropBoundary j t ≤ t := Nat.sub_le _ _
  omega

theorem arrayLoop_execution (g : BitString  →  ℕ) (j : ℕ) (xs : List ℕ) (N : ℕ)
    (hxs : ∀ t∈xs,t ≤ N) (output : BitString) :
    ∃cost, WhileExecution (0:Fin 8) skip arrayBody g
      (arrayStore (natBits xs) (unary j) [] output [] [] [] [])
      (arrayStore [] (unary j) [] ((natBits (xs.map (dropBoundary j))).reverse++output) [] [] [] []) cost ∧
      cost ≤ 1+xs.length*(24*N+13*j+48) := by
  induction xs generalizing output with
  | nil => exact ⟨1,by simpa [natBits,natWords,encodeBitList] using
      (WhileExecution.empty (stack:=(0:Fin 8)) (B:=skip) (C:=arrayBody) (g:=g)
        (arrayStore [] (unary j) [] output [] [] [] []) rfl),by simp⟩
  | cons t xs ih =>
    obtain ⟨cb,hb,hbb⟩ := arrayBody_executes g j t (natBits xs) output
    obtain ⟨ct,ht,hbt⟩ := ih (fun t ht => hxs t (by simp [ht]))
      ((true::pairBits (unary (dropBoundary j t)) []).reverse++output)
    have h := WhileExecution.one (stack:=(0:Fin 8)) (B:=skip) (C:=arrayBody) (g:=g)
      (s:=arrayStore (natBits (t::xs)) (unary j) [] output [] [] [] [])
      (rest:=pairBits (unary t) (natBits xs)) rfl
      (by convert hb using 1;funext i;fin_cases i <;> rfl) ht
    refine ⟨2+cb+ct,?_,?_⟩
    · convert h using 1
      · simp [natBits,natWords,encodeBitList_cons_segment,List.reverse_append,List.append_assoc]
      · omega
    · have hn := hxs t (by simp)
      simp only [List.length_cons]
      nlinarith

lemma natBits_length_bound (xs : List ℕ) (N : ℕ) (hxs : ∀ t∈xs,t ≤ N) :
    (natBits xs).length ≤ 2*xs.length*(N+1) := by
  apply (encodedWords_length_bound (natWords xs) N ?_).trans_eq
  · simp [natWords]
  · intro word hw
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hw
    simpa using hxs t ht

theorem arrayMap_executes (g : BitString  →  ℕ) (j : ℕ) (xs : List ℕ) (N : ℕ)
    (hxs : ∀ t∈xs,t ≤ N) :
    ∃cost, arrayMap.Executes g (arrayStore (natBits xs) (unary j) [] [] [] [] [] [])
      (arrayStore (natBits (xs.map (dropBoundary j))) (unary j) [] [] [] [] [] []) cost ∧
      cost ≤ xs.length*(28*N+13*j+52)+4 := by
  obtain ⟨cl,hl,hbl⟩ := arrayLoop_execution g j xs N hxs []
  have hl' : arrayLoop.Executes g (arrayStore (natBits xs) (unary j) [] [] [] [] [] [])
      (arrayStore [] (unary j) [] (natBits (xs.map (dropBoundary j))).reverse [] [] [] []) cl := by
    simpa using whilePop_executes _ _ _ _ hl
  have hr : (reverseOn (3:Fin 8) 0 (by decide)).Executes g
      (arrayStore [] (unary j) [] (natBits (xs.map (dropBoundary j))).reverse [] [] [] [])
      (arrayStore (natBits (xs.map (dropBoundary j))) (unary j) [] [] [] [] [] [])
      (2*(natBits (xs.map (dropBoundary j))).length+1) := by
    convert reverseOn_executes g (3:Fin 8) 0 (by decide)
      (arrayStore [] (unary j) [] (natBits (xs.map (dropBoundary j))).reverse [] [] [] []) using 1
    · funext i;fin_cases i <;> simp [arrayStore]
    · simp [arrayStore]
  have hlen := natBits_length_bound (xs.map (dropBoundary j)) N (by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    exact (Nat.sub_le _ _).trans (hxs a ha))
  simp only [List.length_map] at hlen
  refine ⟨_,seq_executes _ _ g hl' hr,?_⟩
  nlinarith

lemma arrayMap_queryFree : arrayMap.QueryFree := seq_queryFree _ _
  (whilePop_queryFree _ _ _ skip_queryFree (seq_queryFree _ _ (unpairOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (scalarOn_queryFree _) (emitWordReversed_queryFree _ _)))))
  (reverseOn_queryFree _ _ _)
end HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
