import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSamplingGroupBody

/-! Generate the entire independent confidence sample matrix from one literal
finite fair-bit tape; no request list or sample result is supplied by an oracle. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def sampleGroupLoop : OracleBlock 94 := whilePop 60 sampleGroupBody sampleGroupBody
noncomputable def sampleGroups : OracleBlock 94 := seq sampleGroupLoop (reverseOn 61 6 (by decide))

 theorem groupWords_length_bound (groups : List (List BitString)) (M B : ℕ)
    (hM : ∀ xs ∈ groups, xs.length ≤ M) (hB : ∀ xs ∈ groups, ∀ x ∈ xs, x.length ≤ B) :
    (groupWords groups).length ≤ 2*groups.length*(2*M*(B+1)+1) := by
  apply (encodedWords_length_bound (groups.map encodeBitList) (2*M*(B+1)) ?_).trans_eq
  · simp
  · intro word hw
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hw
    apply (encodedWords_length_bound xs B (hB xs hxs)).trans
    gcongr
    exact hM xs hxs

 theorem sampleGroupLoop_execution (g : BitString → ℕ) (context rest out : BitString)
    (groups : List (List BitString)) (width batch B : ℕ)
    (hbatch : ∀ blocks ∈ groups, blocks.length=batch)
    (hwidth : ∀ blocks ∈ groups, ∀ bits ∈ blocks, bits.length=width)
    (hB : ∀ blocks ∈ groups, ∀ word ∈ sampledWords context blocks, word.length ≤ B) :
    ∃ t, WhileExecution (60 : Fin 95) sampleGroupBody sampleGroupBody g
      (sampleGridStore (groups.flatten.flatten++rest) context out width batch groups.length 0 [])
      (sampleGridStore rest context ((groupWords (groups.map (sampledWords context))).reverse++out) width batch 0 0 []) t ∧
      t ≤ 1+groups.length*sampleGroupBound context.length width batch B := by
  induction groups generalizing out with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [groupWords,encodeBitList] using
      (WhileExecution.empty (sampleGridStore rest context out width batch 0 0 []) (by rfl))
  | cons blocks groups ih =>
    obtain ⟨tb,hb,hbt⟩ := sampleGroupBody_executes g context (groups.flatten.flatten++rest) out
      blocks width batch groups.length B (hbatch blocks (by simp)) (hwidth blocks (by simp)) (hB blocks (by simp))
    obtain ⟨tt,ht,htt⟩ := ih
      ((true::pairBits (encodeBitList (sampledWords context blocks)) []).reverse++out)
      (fun blocks hb => hbatch blocks (by simp [hb]))
      (fun blocks hb => hwidth blocks (by simp [hb]))
      (fun blocks hb => hB blocks (by simp [hb]))
    have hpop : Function.update
        (sampleGridStore ((blocks::groups).flatten.flatten++rest) context out width batch (blocks::groups).length 0 [])
        (60 : Fin 95) (List.replicate groups.length true) =
        sampleGridStore (blocks.flatten++(groups.flatten.flatten++rest)) context out width batch groups.length 0 [] := by
      funext i; fin_cases i <;> simp [sampleGridStore,List.flatten_cons,List.flatten_append,List.append_assoc]
    have hw := WhileExecution.one
      (s := sampleGridStore ((blocks::groups).flatten.flatten++rest) context out width batch (blocks::groups).length 0 [])
      (rest := List.replicate groups.length true) (by rfl) (by rw [hpop]; exact hb) ht
    refine ⟨2+tb+tt,?_,?_⟩
    · convert hw using 1
      · simp only [List.map_cons,groupWords,List.map_cons,encodeBitList_cons_segment,List.reverse_append,List.append_assoc]
      · omega
    · simp only [List.length_cons]; nlinarith

 theorem sampleGroups_executes (g : BitString → ℕ) (context rest : BitString)
    (groups : List (List BitString)) (width batch B : ℕ)
    (hbatch : ∀ blocks ∈ groups, blocks.length=batch)
    (hwidth : ∀ blocks ∈ groups, ∀ bits ∈ blocks, bits.length=width)
    (hB : ∀ blocks ∈ groups, ∀ word ∈ sampledWords context blocks, word.length ≤ B) :
    ∃ t, sampleGroups.Executes g
      (sampleGridStore (groups.flatten.flatten++rest) context [] width batch groups.length 0 [])
      (sampleGridStore rest context [] width batch 0 0 (groupWords (groups.map (sampledWords context)))) t ∧
      t ≤ groups.length*sampleGroupBound context.length width batch B+
        4*groups.length*(2*batch*(B+1)+1)+4 := by
  obtain ⟨tl,hl,hbl⟩ := sampleGroupLoop_execution g context rest [] groups width batch B hbatch hwidth hB
  have hloop : sampleGroupLoop.Executes g
      (sampleGridStore (groups.flatten.flatten++rest) context [] width batch groups.length 0 [])
      (sampleGridStore rest context (groupWords (groups.map (sampledWords context))).reverse width batch 0 0 []) tl := by
    simpa using whilePop_executes _ _ _ _ hl
  have hr : (reverseOn (61 : Fin 95) 6 (by decide)).Executes g
      (sampleGridStore rest context (groupWords (groups.map (sampledWords context))).reverse width batch 0 0 [])
      (sampleGridStore rest context [] width batch 0 0 (groupWords (groups.map (sampledWords context))))
      (2*(groupWords (groups.map (sampledWords context))).length+1) := by
    convert reverseOn_executes g (61 : Fin 95) 6 (by decide)
      (sampleGridStore rest context (groupWords (groups.map (sampledWords context))).reverse width batch 0 0 []) using 1
    · funext i; fin_cases i <;> simp [sampleGridStore]
    · simp [sampleGridStore]
  have hlen := groupWords_length_bound (groups.map (sampledWords context)) batch B
    (by intro xs hx; obtain ⟨blocks,hblocks,rfl⟩ := List.mem_map.mp hx; simp [sampledWords,hbatch blocks hblocks])
    (by intro xs hx; obtain ⟨blocks,hblocks,rfl⟩ := List.mem_map.mp hx; exact hB blocks hblocks)
  simp only [List.length_map] at hlen
  refine ⟨_,seq_executes _ _ g hloop hr,?_⟩
  nlinarith

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
