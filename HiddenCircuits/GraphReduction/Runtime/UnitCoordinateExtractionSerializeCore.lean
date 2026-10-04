import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerializeLoop

/-! Preserve the unary coordinate array and denominator, stream a physical copy,
and reverse the completed native coordinate representation into the output. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

noncomputable def coreProgram : OracleBlock 8 := seq (copyOn 0 3 7 (by decide) (by decide) (by decide))
  (seq header (seq loop (reverseOn 8 2 (by decide))))
def bound (n D B : ℕ) : ℕ := cellBound D+n*(cellBound B+14*B+20)+4*D+20

lemma coreProgram_executes (g : BitString → ℕ) (D : ℕ) (xs : List ℕ) (B : ℕ)
    (hx : ∀a∈xs,a≤B) :
    ∃t,coreProgram.Executes g (coreState (encodeBitList (unaryWords xs)) D [] [] [] [] [])
      (coreState (encodeBitList (unaryWords xs)) D (nativeBytes D xs) [] [] [] []) t ∧
      t≤bound xs.length D B := by
  let values:=encodeBitList (unaryWords xs)
  have hc : (copyOn (0:Fin 9) 3 7 (by decide) (by decide) (by decide)).Executes g
      (coreState values D [] [] [] [] []) (coreState values D [] values [] [] []) (5*values.length+2) := by
    convert copyOn_executes g (0:Fin 9) 3 7 (by decide) (by decide) (by decide)
      (coreState values D [] [] [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [coreState]
  obtain ⟨h,hh,hb⟩:=header_executes g values D values []
  simp only [List.append_nil] at hh
  obtain ⟨l,hl,lb⟩:=loop_executes g values D xs (wordChunk (signedBits (D:ℤ))).reverse B hx
  have he:(encodeBitList (binaryWords xs)).reverse++(wordChunk (signedBits (D:ℤ))).reverse=
      (nativeBytes D xs).reverse := by
    simp [nativeBytes,encodeBitList_eq_chunks,List.reverse_append]
  rw [he] at hl
  have hr : (reverseOn (8:Fin 9) 2 (by decide)).Executes g
      (coreState values D [] [] [] [] (nativeBytes D xs).reverse)
      (coreState values D (nativeBytes D xs) [] [] [] []) (2*(nativeBytes D xs).length+1) := by
    convert reverseOn_executes g (8:Fin 9) 2 (by decide)
      (coreState values D [] [] [] [] (nativeBytes D xs).reverse) using 1
    · funext i;fin_cases i <;> simp [coreState]
    · simp [coreState]
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hh (seq_executes _ _ g hl hr)),?_⟩
  have hv:=unary_stream_length xs B hx
  have ho:=native_length D xs B hx
  change values.length≤_ at hv
  unfold bound
  nlinarith

lemma coreProgram_queryFree : coreProgram.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ header_queryFree (seq_queryFree _ _ loop_queryFree (reverseOn_queryFree _ _ _)))
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionSerialize
