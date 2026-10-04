import HiddenCircuits.Approximation.SelfReduction.Runtime.RequestLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.SamplerBatch

/-! A concrete contiguous-coin request generator followed by the actual
monotone sampler batch. Persistent context and unused random suffix are framed. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def requestPorts : Fin 11 ↪ Fin 59 where
  toFun i := i.castAdd 48
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 59 => x.val) h)

def samplePorts : Fin 49 ↪ Fin 59 where
  toFun i := if i=0 then 6 else ⟨i.val+10,by omega⟩
  inj' := by
    intro i j h
    by_cases hi : i=0 <;> by_cases hj : j=0
    · simpa [hi,hj]
    · have hh := congrArg (fun x : Fin 59 => x.val) h; simp [hi,hj] at hh <;> omega
    · have hh := congrArg (fun x : Fin 59 => x.val) h; simp [hi,hj] at hh <;> omega
    · apply Fin.ext; have hh := congrArg (fun x : Fin 59 => x.val) h; simp [hi,hj] at hh <;> omega

def samplingStore (coins context : BitString) (width count : ℕ) (data : BitString) : Store 58 := fun i =>
  if i.val=0 then coins else if i.val=1 then context else if i.val=2 then List.replicate width true
  else if i.val=3 then List.replicate count true else if i.val=6 then data else []

noncomputable def samplingRequests : OracleBlock 58 :=
  seq (rename requestGenerator requestPorts) (rename samplerBatch samplePorts)

 theorem samplingRequests_executes (g : BitString → ℕ) (context rest : BitString)
    (blocks : List BitString) (width : ℕ) (hblocks : ∀ bits ∈ blocks, bits.length=width) :
    let N := 2*context.length+width+1
    ∃ t, samplingRequests.Executes g
      (samplingStore (blocks.flatten++rest) context width blocks.length [])
      (samplingStore rest context width 0
        (encodeBitList (blocks.map (fun bits => SamplerRuntime.Functional.evaluate (pairBits context bits))))) t ∧
      t ≤ blocks.length*(22*width+33*context.length+46)+
        6*(blocks.length*(4*context.length+2*width+4))+
        blocks.length*(15*N+11*SamplerRuntime.MonotoneSampler.time.eval N+24)+17 := by
  dsimp only
  let requests := blocks.map (fun bits => pairBits context bits)
  have hgen : (rename requestGenerator requestPorts).Executes g
      (samplingStore (blocks.flatten++rest) context width blocks.length [])
      (samplingStore rest context width 0 (encodeBitList requests))
      (blocks.length*(22*width+33*context.length+46)+4) := by
    apply rename_executes_to requestGenerator requestPorts g (requestGenerator_executes g context rest blocks width hblocks)
    · funext i; fin_cases i <;> simp [samplingStore,requestStore,requestPorts,requests]
    · funext i; fin_cases i <;> simp [samplingStore,requestStore,requestPorts,requests]
    · intro j hj
      have h0 : j.val≠0 := by intro h; exact hj 0 (Fin.ext h.symm)
      have h3 : j.val≠3 := by intro h; exact hj 3 (Fin.ext h.symm)
      have h6 : j.val≠6 := by intro h; exact hj 6 (Fin.ext h.symm)
      simp [samplingStore,h0,h3,h6]
  have hreq : ∀ r ∈ requests, r.length ≤ 2*context.length+width+1 := by
    intro r hr
    obtain ⟨bits,hbits,rfl⟩ := List.mem_map.mp hr
    simp [hblocks bits hbits]
  obtain ⟨t,ht,hb⟩ := samplerBatch_executes g requests _ hreq
  have hbatch : (rename samplerBatch samplePorts).Executes g
      (samplingStore rest context width 0 (encodeBitList requests))
      (samplingStore rest context width 0 (encodeBitList (requests.map SamplerRuntime.Functional.evaluate))) t := by
    apply rename_executes_to samplerBatch samplePorts g ht
    · funext i
      by_cases hi : i=0
      · subst i; simp [samplePorts,samplingStore]
      · have hv : i.val≠0 := by simpa using hi
        have hval : 10 < i.val+10 := by omega
        simp [samplePorts,hi,samplingStore,Function.update_apply] <;> omega
    · funext i
      by_cases hi : i=0
      · subst i; simp [samplePorts,samplingStore]
      · have hv : i.val≠0 := by simpa using hi
        have hval : 10 < i.val+10 := by omega
        simp [samplePorts,hi,samplingStore,Function.update_apply] <;> omega
    · intro j hj
      have h6 : j.val≠6 := by intro h; exact hj 0 (by apply Fin.ext; simpa [samplePorts] using h.symm)
      simp [samplingStore,h6]
  refine ⟨(blocks.length*(22*width+33*context.length+46)+4)+t+2,?_,?_⟩
  · simpa only [samplingRequests,requests,List.map_map,Function.comp_def] using seq_executes _ _ g hgen hbatch
  · dsimp only [requests] at hb
    rw [encoded_requests_length context blocks width hblocks, List.length_map] at hb
    omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
