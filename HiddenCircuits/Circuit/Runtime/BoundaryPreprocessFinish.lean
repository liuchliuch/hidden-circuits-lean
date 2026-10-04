import HiddenCircuits.Circuit.Runtime.BoundaryPreprocess

namespace HiddenCircuits.Circuit.Runtime.BoundaryPreprocess
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

lemma finish_executes (g : BitString→ℕ) (width output : BitString) :
    finish.Executes g (store [] [] [] width output.reverse)
      (store (pairBits width output) [] [] [] []) (2*output.length+10*width.length+12) := by
  have hr : (reverseOn (5:Fin 8) 0 (by decide)).Executes g (store [] [] [] width output.reverse)
      (store output [] [] width []) (2*output.length+1) := by
    convert reverseOn_executes g (5:Fin 8) 0 (by decide) (store [] [] [] width output.reverse) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have hp : (PairSerialization.on pairMap).Executes g (store output [] [] width [])
      (store (pairBits width output) [] [] [] []) (10*width.length+9) := by
    convert PairSerialization.on_executes pairMap g (store output [] [] width []) width output
      (by funext i;fin_cases i <;> rfl) using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g hr hp using 1 <;> omega

lemma store_bound (input left right width out : BitString) (B : ℕ)
    (hi : input.length ≤ B) (hl : left.length ≤ B) (hr : right.length ≤ B)
    (hw : width.length ≤ B) (ho : out.length ≤ B) : ∀i,(store input left right width out i).length ≤ B := by
  intro i;fin_cases i <;> simp [store] <;> assumption
lemma program_executes (g : BitString→ℕ) (left right width gates : BitString) :
    ∃c,program.Executes g (store (input left right width gates) [] [] [] [])
      (store (result left right width gates) [] [] [] []) c ∧
      c ≤ time.eval (input left right width gates).length := by
  let L:=(input left right width gates).length
  have hlen : L=2*left.length+2*right.length+2*width.length+gates.length+3 := by
    dsimp only [L,input];simp only [pairBits_length];omega
  have hl : left.length ≤ L := by omega
  have hr : right.length ≤ L := by omega
  have hw : width.length ≤ L := by omega
  have hg : gates.length ≤ L := by omega
  have hp:=parse_executes g left right width gates
  obtain ⟨e,he,heb⟩:=emit_executes g left right width gates
  have hs:=he.stack_bound (store_bound gates left right width [] L hg hl hr hw (by simp)) (5:Fin 8)
  change (BoundaryTransport.chunks left 0++gates++BoundaryTransport.chunks right 0).reverse.length ≤ L+e at hs
  rw [List.length_reverse] at hs
  have hf:=finish_executes g width (BoundaryTransport.chunks left 0++gates++BoundaryTransport.chunks right 0)
  refine ⟨5*(left.length+right.length+width.length)+25+
    (e+(2*(BoundaryTransport.chunks left 0++gates++BoundaryTransport.chunks right 0).length+10*width.length+12)+2)+2,
    seq_executes _ _ g hp (seq_executes _ _ g he hf),?_⟩
  have heb' : e ≤ 28*L^2+150*L+13 := by nlinarith [sq_nonneg (L-left.length),sq_nonneg (L-right.length)]
  simp only [time,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
  change _ ≤ 500*(L+1)^2
  nlinarith
lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (SamplePairParser.on_queryFree _) (seq_queryFree _ _ (SamplePairParser.on_queryFree _) (SamplePairParser.on_queryFree _)))
  (seq_queryFree _ _ (seq_queryFree _ _ (BoundaryTransport.on_queryFree _)
      (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (BoundaryTransport.on_queryFree _)))
    (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (PairSerialization.on_queryFree _)))
end HiddenCircuits.Circuit.Runtime.BoundaryPreprocess
