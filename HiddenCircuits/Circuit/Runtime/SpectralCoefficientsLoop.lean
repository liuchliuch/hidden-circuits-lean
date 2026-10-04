import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsBody
import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsPure
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsLoop

/-! The entire signed coefficient list is traversed by a fixed finite loop. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCoefficients
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic

noncomputable def streamLoop : OracleBlock 19 := whilePop 16 skip body

theorem streamLoop_executes (g : BitString → ℕ) (a prev : ℤ) (cs : List ℤ) (emitted : BitString) (B : ℕ)
    (ha : (signedBits a).length≤B) (hp : (signedBits prev).length≤B)
    (hc : ∀c∈cs,(signedBits c).length≤B) :
    ∃ t, streamLoop.Executes g (streamStore a prev [] [] [] (encodeBitList (cs.map signedBits)) emitted)
      (streamStore a (lastValue prev cs) [] [] [] []
        ((encodeBitList ((front a prev cs).map signedBits)).reverse++emitted)) t ∧
      t≤cs.length*(bodyTime.eval B+2)+1 := by
  suffices ∃ t, WhileExecution (16:Fin 20) skip body g
      (streamStore a prev [] [] [] (encodeBitList (cs.map signedBits)) emitted)
      (streamStore a (lastValue prev cs) [] [] [] []
        ((encodeBitList ((front a prev cs).map signedBits)).reverse++emitted)) t ∧
      t≤cs.length*(bodyTime.eval B+2)+1 by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction cs generalizing prev emitted with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [front,lastValue,encodeBitList] using (WhileExecution.empty (stack:=(16:Fin 20)) (B:=skip) (C:=body)
      (g:=g) (streamStore a prev [] [] [] [] emitted) rfl)
  | cons c cs ih =>
    have hcc := hc c (by simp)
    obtain ⟨t,ht,htb⟩ := body_executes g a prev c (encodeBitList (cs.map signedBits)) emitted B ha hp hcc
    obtain ⟨u,hu,hub⟩ := ih c ((wordChunk (signedBits (prev-a*c))).reverse++emitted) hcc
      (fun z hz => hc z (by simp [hz]))
    have he : Function.update
        (streamStore a prev [] [] [] (encodeBitList ((c::cs).map signedBits)) emitted) (16:Fin 20)
        (pairBits (signedBits c) (encodeBitList (cs.map signedBits)))=
        streamStore a prev [] [] [] (pairBits (signedBits c) (encodeBitList (cs.map signedBits))) emitted := by
      funext i;fin_cases i <;> rfl
    rw [←he] at ht
    have hh := WhileExecution.one
      (show streamStore a prev [] [] [] (encodeBitList ((c::cs).map signedBits)) emitted 16=
        true::pairBits (signedBits c) (encodeBitList (cs.map signedBits)) from rfl) ht hu
    refine ⟨1+t+1+u,?_,?_⟩
    · simpa [front,lastValue,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc] using hh
    · simp only [List.length_cons]
      nlinarith

noncomputable def finishPass : OracleBlock 19 :=
  seq (copyOn 10 12 2 (by decide) (by decide) (by decide))
    (seq emitCell (reverseOn 17 16 (by decide)))

theorem finishPass_executes (g : BitString → ℕ) (a prev : ℤ) (pre : List ℤ) :
    finishPass.Executes g (streamStore a prev [] [] [] [] (encodeBitList (pre.map signedBits)).reverse)
      (streamStore a prev [] [] [] (encodeBitList ((pre++[prev]).map signedBits)) [])
      (11*(signedBits prev).length+2*(encodeBitList ((pre++[prev]).map signedBits)).length+14) := by
  let out := (encodeBitList (pre.map signedBits)).reverse
  let s₀ := streamStore a prev [] [] [] [] out
  let s₁ := streamStore a prev [] (signedBits prev) [] [] out
  let s₂ := streamStore a prev [] [] [] [] ((wordChunk (signedBits prev)).reverse++out)
  let s₃ := streamStore a prev [] [] [] (encodeBitList ((pre++[prev]).map signedBits)) []
  have h₁ : (copyOn (10:Fin 20) 12 2 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (5*(signedBits prev).length+2) := by
    convert copyOn_executes g (10:Fin 20) 12 2 (by decide) (by decide) (by decide) s₀ rfl using 1
    funext i;fin_cases i <;> simp [s₀,s₁,streamStore]
  have h₂ : emitCell.Executes g s₁ s₂ (6*(signedBits prev).length+7) := emitCell_executes g a prev _ [] out
  have he : (wordChunk (signedBits prev)).reverse++out=(encodeBitList ((pre++[prev]).map signedBits)).reverse := by
    simp [out,encodeBitList_eq_chunks,List.reverse_append]
  have h₃ : (reverseOn (17:Fin 20) 16 (by decide)).Executes g s₂ s₃
      (2*(encodeBitList ((pre++[prev]).map signedBits)).length+1) := by
    have hh := reverseOn_executes g (17:Fin 20) 16 (by decide) s₂
    convert hh using 1
    · funext i;fin_cases i <;> simp [s₂,s₃,streamStore,he,List.reverse_reverse]
    · simp [s₂,streamStore,he]
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃) using 1 <;> omega

noncomputable def pass : OracleBlock 19 := seq streamLoop finishPass

theorem go_signed_length (a prev : ℤ) (cs : List ℤ) (B : ℕ)
    (ha : (signedBits a).length≤B) (hp : (signedBits prev).length≤B)
    (hc : ∀c∈cs,(signedBits c).length≤B) : ∀z∈go a prev cs,(signedBits z).length≤4*B+9 := by
  induction cs generalizing prev with
  | nil => simp only [go,List.mem_singleton];rintro z rfl;omega
  | cons c cs ih =>
    have hcc := hc c (by simp)
    intro z hz
    simp only [go,List.mem_cons] at hz
    rcases hz with rfl|hz
    · exact cell_output_length a prev c B ha hp hcc
    · exact ih c hcc (fun z hz => hc z (by simp [hz])) z hz

theorem pass_executes (g : BitString → ℕ) (a prev : ℤ) (cs : List ℤ) (B : ℕ)
    (ha : (signedBits a).length≤B) (hp : (signedBits prev).length≤B)
    (hc : ∀c∈cs,(signedBits c).length≤B) :
    ∃ t, pass.Executes g (streamStore a prev [] [] [] (encodeBitList (cs.map signedBits)) [])
      (streamStore a (lastValue prev cs) [] [] [] (encodeBitList ((go a prev cs).map signedBits)) []) t ∧
      t≤cs.length*(bodyTime.eval B+2)+11*B+4*(cs.length+1)*(4*B+10)+17 := by
  obtain ⟨t,ht,htb⟩ := streamLoop_executes g a prev cs [] B ha hp hc
  simp only [List.append_nil] at ht
  have hf := finishPass_executes g a (lastValue prev cs) (front a prev cs)
  rw [←go_eq_front] at hf
  refine ⟨t+(11*(signedBits (lastValue prev cs)).length+2*(encodeBitList ((go a prev cs).map signedBits)).length+14)+2,
    seq_executes _ _ g ht hf,?_⟩
  have hp' := lastValue_bound prev cs B hp hc
  have he := encodedWords_length_le ((go a prev cs).map signedBits) (4*B+9) (by
    intro w hw;obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw;exact go_signed_length a prev cs B ha hp hc z hz)
  simp only [List.length_map,go_length] at he
  nlinarith

 theorem pass_queryFree : pass.QueryFree :=
  seq_queryFree _ _ (whilePop_queryFree _ _ _ skip_queryFree body_queryFree)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree)
      (reverseOn_queryFree _ _ _)))
end HiddenCircuits.Circuit.Runtime.SpectralCoefficients
