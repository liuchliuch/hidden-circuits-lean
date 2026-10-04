import HiddenCircuits.Circuit.Runtime.WordCount
import HiddenCircuits.Complexity.WordEncoding

/-! The canonical word header, two boundary masks and actual letter count are
read from the input bit stream. The original input and sample index are kept. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WordParser
open Complexity OracleBlock
set_option maxHeartbeats 600000

def store (input header source target letters count sample : BitString) : Store 17 := fun i =>
  if i.val=0 then input else if i.val=1 then header else if i.val=2 then source
  else if i.val=3 then target else if i.val=4 then letters else if i.val=5 then count
  else if i.val=6 then sample else []

def parseEmbedding (dst : Fin 4) : Fin 4 ↪ Fin 18 where
  toFun i := if i.val=0 then 4 else if i.val=1 then ⟨dst.val,by omega⟩ else if i.val=2 then 7 else 8
  inj' := by intro i j h;fin_cases dst <;> fin_cases i <;> fin_cases j <;> simp_all
noncomputable def parse (dst : Fin 4) : OracleBlock 17 := Circuit.Runtime.SamplePairParser.on (parseEmbedding dst)
noncomputable def listHead (dst : Fin 4) : OracleBlock 17 := branchPop 4 skip (parse dst) (parse dst)
def countEmbedding : Fin 6 ↪ Fin 18 where
  toFun i := (![4,7,8,9,10,5] : Fin 6 → Fin 18) i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 17 := seq (copyOn 0 4 7 (by decide) (by decide) (by decide))
  (seq (parse 1) (seq (listHead 2) (seq (listHead 3) (Circuit.Runtime.WordCount.on countEmbedding))))

lemma parse_executes (g : BitString → ℕ) (dst : Fin 4) (s t : Store 17) (x y : BitString)
    (hs : s ∘ parseEmbedding dst=GraphVerifier.Runtime.parseStore (pairBits x y) [] [] [])
    (ht : t ∘ parseEmbedding dst=GraphVerifier.Runtime.parseStore y x [] [])
    (hf : ∀i,(∀j,parseEmbedding dst j≠i)→t i=s i) :
    (parse dst).Executes g s t (5*x.length+7) :=
  Circuit.Runtime.SamplePairParser.on_executes _ g x y s t hs ht hf

lemma head_executes (g : BitString → ℕ) (dst : Fin 4) (s t : Store 17) (x y : BitString)
    (h4 : s 4=true::pairBits x y)
    (hs : (Function.update s 4 (pairBits x y)) ∘ parseEmbedding dst=GraphVerifier.Runtime.parseStore (pairBits x y) [] [] [])
    (ht : t ∘ parseEmbedding dst=GraphVerifier.Runtime.parseStore y x [] [])
    (hf : ∀i,(∀j,parseEmbedding dst j≠i)→t i=(Function.update s 4 (pairBits x y)) i) :
    (listHead dst).Executes g s t (5*x.length+9) := by
  convert branchPop_true 4 skip (parse dst) (parse dst) g h4 (parse_executes g dst _ _ x y hs ht hf) using 1 <;> omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (Circuit.Runtime.SamplePairParser.on_queryFree _)
    (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree (Circuit.Runtime.SamplePairParser.on_queryFree _) (Circuit.Runtime.SamplePairParser.on_queryFree _))
      (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree (Circuit.Runtime.SamplePairParser.on_queryFree _) (Circuit.Runtime.SamplePairParser.on_queryFree _))
        (Circuit.Runtime.WordCount.on_queryFree _))))

end HiddenCircuits.GraphReduction.Runtime.WordGraph.WordParser
