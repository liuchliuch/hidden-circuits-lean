import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSamplingRequests
import HiddenCircuits.Approximation.SelfReduction.Runtime.GroupTallyLoop

/-! One real sample-group iteration consumes a fresh block of random coins,
calls the concrete initialized sampler, decodes partners, and emits a nested
group. Width, sample count and graph context are preserved. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def sampleGridStore (coins context out : BitString) (width batch remaining clock : ℕ) (result : BitString) : Store 94 := fun i =>
  if i.val=0 then coins else if i.val=1 then context else if i.val=2 then List.replicate width true
  else if i.val=3 then List.replicate clock true else if i.val=6 then result
  else if i.val=59 then List.replicate batch true else if i.val=60 then List.replicate remaining true
  else if i.val=61 then out else []

def sampleGridPorts : Fin 92 ↪ Fin 95 where
  toFun i := ⟨if i.val < 59 then i.val else i.val+3, by split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun x : Fin 95 => x.val) h
    dsimp at hh
    split_ifs at hh <;> omega

noncomputable def sampleGroupBody : OracleBlock 94 :=
  seq (copyOn 59 3 4 (by decide) (by decide) (by decide))
    (seq (rename partnerRequests sampleGridPorts) (emitWordReversed 6 61))

noncomputable def sampledWords (context : BitString) (blocks : List BitString) : List BitString :=
  blocks.map (fun bits => partnerEvaluate (pairBits context bits))

noncomputable def sampleGroupBound (C width M B : ℕ) : ℕ :=
  let N := 2*C+width+1
  M*(22*width+33*C+46)+6*(M*(4*C+2*width+4))+
    M*(15*N+11*partnerTime.eval N+24)+5*M+12*M*(B+1)+32

 theorem sampleGroupBody_executes (g : BitString → ℕ) (context rest out : BitString)
    (blocks : List BitString) (width batch remaining B : ℕ) (hbatch : blocks.length=batch)
    (hwidth : ∀ bits ∈ blocks, bits.length=width)
    (hB : ∀ word ∈ sampledWords context blocks, word.length ≤ B) :
    ∃ t, sampleGroupBody.Executes g
      (sampleGridStore (blocks.flatten++rest) context out width batch remaining 0 [])
      (sampleGridStore rest context
        ((true::pairBits (encodeBitList (sampledWords context blocks)) []).reverse++out) width batch remaining 0 []) t ∧
      t+2 ≤ sampleGroupBound context.length width batch B := by
  have h1 : (copyOn (59 : Fin 95) 3 4 (by decide) (by decide) (by decide)).Executes g
      (sampleGridStore (blocks.flatten++rest) context out width batch remaining 0 [])
      (sampleGridStore (blocks.flatten++rest) context out width batch remaining batch []) (5*batch+2) := by
    convert copyOn_executes g (59 : Fin 95) 3 4 (by decide) (by decide) (by decide)
      (sampleGridStore (blocks.flatten++rest) context out width batch remaining 0 []) rfl using 1
    · funext i; fin_cases i <;> simp [sampleGridStore]
    · simp [sampleGridStore]
  obtain ⟨ts,hs,hbs⟩ := partnerRequests_executes g context rest blocks width hwidth
  have h2 : (rename partnerRequests sampleGridPorts).Executes g
      (sampleGridStore (blocks.flatten++rest) context out width batch remaining batch [])
      (sampleGridStore rest context out width batch remaining 0 (encodeBitList (sampledWords context blocks))) ts := by
    apply rename_executes_to partnerRequests sampleGridPorts g hs
    · funext i; fin_cases i <;> simp [sampleGridStore,samplingStore,sampleGridPorts,hbatch]
    · funext i; fin_cases i <;> simp [sampleGridStore,samplingStore,sampleGridPorts,sampledWords]
    · intro j hj
      have h0 : j.val≠0 := by intro h; exact hj 0 (Fin.ext h.symm)
      have h3 : j.val≠3 := by intro h; exact hj 3 (Fin.ext h.symm)
      have h6 : j.val≠6 := by intro h; exact hj 6 (Fin.ext h.symm)
      simp [sampleGridStore,h0,h3,h6]
  have h3 : (emitWordReversed (6 : Fin 95) 61).Executes g
      (sampleGridStore rest context out width batch remaining 0 (encodeBitList (sampledWords context blocks)))
      (sampleGridStore rest context ((true::pairBits (encodeBitList (sampledWords context blocks)) []).reverse++out)
        width batch remaining 0 []) (6*(encodeBitList (sampledWords context blocks)).length+7) := by
    convert emitWordReversed_executes g (6 : Fin 95) 61 (by decide)
      (sampleGridStore rest context out width batch remaining 0 (encodeBitList (sampledWords context blocks))) using 1
    funext i; fin_cases i <;> simp [sampleGridStore]
  have hlen := encodedWords_length_bound (sampledWords context blocks) B hB
  simp only [sampledWords,List.length_map,hbatch] at hlen
  rw [hbatch] at hbs
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  dsimp only [sampleGroupBound,sampledWords]
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
