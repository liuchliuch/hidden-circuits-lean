import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

namespace HiddenCircuits.GraphReduction.Runtime.TripleSerialization
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def state (a rb rc out wb wc final : BitString) : Store 7 := ![a,rb,rc,out,wb,wc,final,[]]
def wordEmbedding (which : Fin 3) : Fin 2 ↪ Fin 8 where
  toFun i := ![(![0,4,5]:Fin 3→Fin 8) which,3] i
  inj' := by fin_cases which <;> decide +kernel
noncomputable def emit (which : Fin 3) : OracleBlock 7 := rename wordEmit (wordEmbedding which)
noncomputable def program : OracleBlock 7 := seq (reverseOn 1 4 (by decide))
  (seq (reverseOn 2 5 (by decide)) (seq (emit 0) (seq (emit 1) (seq (emit 2) (reverseOn 3 6 (by decide))))))

theorem emit0 (g : BitString → ℕ) (a b c out : BitString) :
    (emit 0).Executes g (state a [] [] out b c []) (state [] [] [] ((wordChunk a).reverse++out) b c []) (6*a.length+7) := by
  apply rename_executes_to _ (wordEmbedding 0) g (wordEmit_executes g a out)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
theorem emit1 (g : BitString → ℕ) (b c out : BitString) :
    (emit 1).Executes g (state [] [] [] out b c []) (state [] [] [] ((wordChunk b).reverse++out) [] c []) (6*b.length+7) := by
  apply rename_executes_to _ (wordEmbedding 1) g (wordEmit_executes g b out)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
theorem emit2 (g : BitString → ℕ) (c out : BitString) :
    (emit 2).Executes g (state [] [] [] out [] c []) (state [] [] [] ((wordChunk c).reverse++out) [] [] []) (6*c.length+7) := by
  apply rename_executes_to _ (wordEmbedding 2) g (wordEmit_executes g c out)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)

theorem program_executes (g : BitString → ℕ) (a b c : BitString) :
    program.Executes g (state a b.reverse c.reverse [] [] [] [])
      (state [] [] [] [] [] [] (encodeBitList [a,b,c])) (10*a.length+12*b.length+12*c.length+46) := by
  have h1 : (reverseOn (1:Fin 8) 4 (by decide)).Executes g (state a b.reverse c.reverse [] [] [] [])
      (state a [] c.reverse [] b [] []) (2*b.length+1) := by
    convert reverseOn_executes g (1:Fin 8) 4 (by decide) (state a b.reverse c.reverse [] [] [] []) using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h2 : (reverseOn (2:Fin 8) 5 (by decide)).Executes g (state a [] c.reverse [] b [] [])
      (state a [] [] [] b c []) (2*c.length+1) := by
    convert reverseOn_executes g (2:Fin 8) 5 (by decide) (state a [] c.reverse [] b [] []) using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  have h3:=emit0 g a b c []
  simp only [List.append_nil] at h3
  have h4:=emit1 g b c (wordChunk a).reverse
  have h5:=emit2 g c ((wordChunk b).reverse++(wordChunk a).reverse)
  let out:=(wordChunk c).reverse++((wordChunk b).reverse++(wordChunk a).reverse)
  have h6 : (reverseOn (3:Fin 8) 6 (by decide)).Executes g (state [] [] [] out [] [] [])
      (state [] [] [] [] [] [] (encodeBitList [a,b,c])) (2*out.length+1) := by
    convert reverseOn_executes g (3:Fin 8) 6 (by decide) (state [] [] [] out [] [] []) using 1
    funext i;fin_cases i <;> simp [state,out,encodeBitList_eq_chunks,List.append_assoc]
  have ht:=seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 h6))))
  convert ht using 1
  simp [out,wordChunk]
  omega
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (reverseOn_queryFree _ _ _)
  (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree)
      (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree) (reverseOn_queryFree _ _ _)))))
end HiddenCircuits.GraphReduction.Runtime.TripleSerialization
