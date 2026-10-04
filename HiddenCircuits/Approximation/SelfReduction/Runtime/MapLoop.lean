import HiddenCircuits.Approximation.SelfReduction.Runtime.MapBody
import HiddenCircuits.Complexity.OracleMove

/-! Fully charged repeated execution of a supplied concrete finite sampler.
The body is an actual instruction block, not a unit-cost function oracle. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def mapResultsLoop {k : ℕ} (B : OracleBlock k) : OracleBlock (k+4) :=
  whilePop (mapRight k 0) skip (mapBody B)
noncomputable def mapResults {k : ℕ} (B : OracleBlock k) : OracleBlock (k+4) :=
  seq (mapResultsLoop B) (reverseOn (mapRight k 1) 0 (mapRight_ne_zero k 1))
noncomputable def mapProgram {k : ℕ} (B : OracleBlock k) : OracleBlock (k+4) :=
  seq (moveOn 0 (mapRight k 0) (mapRight k 2) (mapRight_ne_zero k 0).symm
    (mapRight_ne_zero k 2).symm ((mapRight k).injective.ne (by decide))) (mapResults B)

 theorem encodeBitList_cons_segment (word : BitString) (xs : List BitString) :
    encodeBitList (word::xs) = (true::pairBits word []) ++ encodeBitList xs := by
  simp [encodeBitList,pairBits_eq_escaped]

 theorem encodedWords_length_bound (xs : List BitString) (N : ℕ) (hxs : ∀ word ∈ xs, word.length ≤ N) :
    (encodeBitList xs).length ≤ 2*xs.length*(N+1) := by
  induction xs with
  | nil => simp [encodeBitList]
  | cons word xs ih =>
    have hw := hxs word (by simp)
    have ht := ih (fun w hw => hxs w (by simp [hw]))
    simp only [encodeBitList,List.length_cons,pairBits_length]
    nlinarith

 theorem mapResultsLoop_execution {k : ℕ} (B : OracleBlock k) (f : BitString → BitString)
    (g : BitString → ℕ) (xs : List BitString) (N T : ℕ)
    (hxs : ∀ word ∈ xs, word.length ≤ N)
    (hB : ∀ word ∈ xs, ∃ cost, B.Executes g (Function.update (fun _ => []) 0 word)
      (Function.update (fun _ => []) 0 (f word)) cost ∧ cost ≤ T) (out : BitString) :
    ∃ t, WhileExecution (mapRight k 0) skip (mapBody B) g
      (mapStore k [] (encodeBitList xs) out [] [])
      (mapStore k [] [] ((encodeBitList (xs.map f)).reverse ++ out) [] []) t ∧
      t ≤ 1+xs.length*(11*N+7*T+20) := by
  induction xs generalizing out with
  | nil =>
    refine ⟨1,?_,by simp⟩
    apply WhileExecution.empty
    simp [encodeBitList]
  | cons word xs ih =>
    obtain ⟨cost,hcall,hcost⟩ := hB word (by simp)
    obtain ⟨tb,hb,hbt⟩ := mapBody_executes B g word (f word) (encodeBitList xs) out cost hcall
    obtain ⟨tt,ht,htt⟩ := ih (fun w hw => hxs w (by simp [hw]))
      (fun w hw => hB w (by simp [hw])) ((true::pairBits (f word) []).reverse ++ out)
    have hw := WhileExecution.one
      (s := mapStore k [] (encodeBitList (word::xs)) out [] [])
      (rest := pairBits word (encodeBitList xs))
      (by simp [encodeBitList]) (by simpa using hb) ht
    refine ⟨2+tb+tt,?_,?_⟩
    · convert hw using 1
      · simp only [List.map_cons, encodeBitList_cons_segment, List.reverse_append, List.append_assoc]
      · omega
    · have hwlen := hxs word (by simp)
      have hb' : tb+2 ≤ 11*N+7*T+20 := by omega
      simp only [List.length_cons]
      nlinarith

 theorem mapResults_executes {k : ℕ} (B : OracleBlock k) (f : BitString → BitString)
    (g : BitString → ℕ) (xs : List BitString) (N T : ℕ)
    (hxs : ∀ word ∈ xs, word.length ≤ N)
    (hB : ∀ word ∈ xs, ∃ cost, B.Executes g (Function.update (fun _ => []) 0 word)
      (Function.update (fun _ => []) 0 (f word)) cost ∧ cost ≤ T) :
    ∃ t, (mapResults B).Executes g (mapStore k [] (encodeBitList xs) [] [] [])
      (mapStore k (encodeBitList (xs.map f)) [] [] [] []) t ∧
      t ≤ xs.length*(15*N+11*T+24)+4 := by
  obtain ⟨tl,hl,hbl⟩ := mapResultsLoop_execution B f g xs N T hxs hB []
  have hr : (reverseOn (mapRight k 1) 0 (mapRight_ne_zero k 1)).Executes g
      (mapStore k [] [] (encodeBitList (xs.map f)).reverse [] [])
      (mapStore k (encodeBitList (xs.map f)) [] [] [] [])
      (2*(encodeBitList (xs.map f)).length+1) := by
    simpa only [mapStore_output,mapStore_zero,List.append_nil,List.reverse_reverse,List.length_reverse,
      mapStore_update_output,mapStore_update_zero] using reverseOn_executes g (mapRight k 1) 0 (mapRight_ne_zero k 1)
      (mapStore k [] [] (encodeBitList (xs.map f)).reverse [] [])
  have hout : ∀ y ∈ xs.map f, y.length ≤ N+T := by
    intro y hy
    obtain ⟨word,hw,rfl⟩ := List.mem_map.mp hy
    obtain ⟨cost,hcall,hcost⟩ := hB word hw
    exact (cleanCall_output_length B g word (f word) cost hcall).trans (Nat.add_le_add (hxs word hw) hcost)
  have hlen := encodedWords_length_bound (xs.map f) (N+T) hout
  simp only [List.length_map] at hlen
  have hloop : (mapResultsLoop B).Executes g (mapStore k [] (encodeBitList xs) [] [] [])
      (mapStore k [] [] (encodeBitList (xs.map f)).reverse [] []) tl := by
    simpa using whilePop_executes _ _ _ _ hl
  refine ⟨_,seq_executes _ _ g hloop hr,?_⟩
  nlinarith

 theorem mapStore_clean (k : ℕ) (word : BitString) :
    mapStore k word [] [] [] []=Function.update (fun _ => []) 0 word := by
  apply mapStore_ext
  · intro i; simp [Function.update_apply]
  · intro i; fin_cases i <;> simp [Function.update_of_ne (mapRight_ne_zero _ _)] <;> rfl

/-- One fixed actual bit program performs all requested calls, with copying,
parsing, output growth, ordering and cleanup included in the polynomial bound. -/
theorem mapProgram_executes {k : ℕ} (B : OracleBlock k) (f : BitString → BitString)
    (g : BitString → ℕ) (xs : List BitString) (N T : ℕ)
    (hxs : ∀ word ∈ xs, word.length ≤ N)
    (hB : ∀ word ∈ xs, ∃ cost, B.Executes g (Function.update (fun _ => []) 0 word)
      (Function.update (fun _ => []) 0 (f word)) cost ∧ cost ≤ T) :
    ∃ t, (mapProgram B).Executes g (Function.update (fun _ => []) 0 (encodeBitList xs))
      (Function.update (fun _ => []) 0 (encodeBitList (xs.map f))) t ∧
      t ≤ 6*(encodeBitList xs).length+xs.length*(15*N+11*T+24)+11 := by
  have hm : (moveOn (0 : Fin (k+5)) (mapRight k 0) (mapRight k 2) (mapRight_ne_zero k 0).symm
      (mapRight_ne_zero k 2).symm ((mapRight k).injective.ne (by decide))).Executes g
      (mapStore k (encodeBitList xs) [] [] [] []) (mapStore k [] (encodeBitList xs) [] [] [])
      (6*(encodeBitList xs).length+5) := by
    simpa using moveOn_executes g (0 : Fin (k+5)) (mapRight k 0) (mapRight k 2)
      (mapRight_ne_zero k 0).symm (mapRight_ne_zero k 2).symm ((mapRight k).injective.ne (by decide))
      (mapStore k (encodeBitList xs) [] [] [] []) (by simp)
  obtain ⟨tr,hr,hbr⟩ := mapResults_executes B f g xs N T hxs hB
  have h := seq_executes _ _ g hm hr
  rw [mapStore_clean,mapStore_clean] at h
  exact ⟨_,h,by omega⟩

 theorem mapProgram_queryFree {k : ℕ} (B : OracleBlock k) (hB : B.QueryFree) :
    (mapProgram B).QueryFree := by
  have hp : (mapParse k).QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have hc : (mapCall B).QueryFree := rename_queryFree _ _ hB
  have hb : (mapBody B).QueryFree := seq_queryFree _ _ hp
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ hc (emitWordReversed_queryFree _ _)))
  have hl : (mapResultsLoop B).QueryFree := whilePop_queryFree _ _ _ skip_queryFree hb
  have hr : (mapResults B).QueryFree := seq_queryFree _ _ hl (reverseOn_queryFree _ _ _)
  exact seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) hr

end HiddenCircuits.Approximation.SelfReduction.Runtime
