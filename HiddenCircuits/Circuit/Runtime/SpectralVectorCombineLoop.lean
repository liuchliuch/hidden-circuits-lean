import HiddenCircuits.Circuit.Runtime.SpectralVectorCombineCell
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsLoop

/-! Full finite traversal of the two equal-length canonical coefficient streams. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralVectorCombine
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

noncomputable def loop : OracleBlock 20 := whilePop 16 skip body

theorem loop_executes (g : BitString → ℕ) (scale : ℤ) (ps : List (ℤ×ℤ)) (emitted : BitString) (B : ℕ)
    (hs : (signedBits scale).length≤B)
    (hp : ∀p∈ps,(signedBits p.1).length≤B ∧ (signedBits p.2).length≤B) :
    ∃ t, loop.Executes g (store scale [] [] [] [] (encodeBitList (ps.map (fun p => signedBits p.1)))
        (encodeBitList (ps.map (fun p => signedBits p.2))) emitted)
      (store scale [] [] [] [] [] [] ((encodeBitList ((output scale ps).map signedBits)).reverse++emitted)) t ∧
      t≤ps.length*(bodyTime.eval B+2)+1 := by
  suffices ∃ t, WhileExecution (16:Fin 21) skip body g
      (store scale [] [] [] [] (encodeBitList (ps.map (fun p => signedBits p.1)))
        (encodeBitList (ps.map (fun p => signedBits p.2))) emitted)
      (store scale [] [] [] [] [] [] ((encodeBitList ((output scale ps).map signedBits)).reverse++emitted)) t ∧
      t≤ps.length*(bodyTime.eval B+2)+1 by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction ps generalizing emitted with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [output,encodeBitList] using (WhileExecution.empty (stack:=(16:Fin 21)) (B:=skip) (C:=body)
      (g:=g) (store scale [] [] [] [] [] [] emitted) rfl)
  | cons p ps ih =>
    obtain ⟨u,v⟩ := p
    obtain ⟨hu,hv⟩ := hp (u,v) (by simp)
    obtain ⟨t,ht,htb⟩ := body_executes g scale u v (encodeBitList (ps.map (fun p => signedBits p.1)))
      (encodeBitList (ps.map (fun p => signedBits p.2))) emitted B hs hu hv
    obtain ⟨c,hc,hcb⟩ := ih ((wordChunk (signedBits (v+scale*u))).reverse++emitted)
      (fun p hp' => hp p (by simp [hp']))
    have he : Function.update
        (store scale [] [] [] [] (encodeBitList (((u,v)::ps).map (fun p => signedBits p.1)))
          (encodeBitList (((u,v)::ps).map (fun p => signedBits p.2))) emitted) (16:Fin 21)
        (pairBits (signedBits u) (encodeBitList (ps.map (fun p => signedBits p.1))))=
        store scale [] [] [] [] (pairBits (signedBits u) (encodeBitList (ps.map (fun p => signedBits p.1))))
          (true::pairBits (signedBits v) (encodeBitList (ps.map (fun p => signedBits p.2)))) emitted := by
      funext i;fin_cases i <;> rfl
    rw [←he] at ht
    have hh := WhileExecution.one
      (show store scale [] [] [] [] (encodeBitList (((u,v)::ps).map (fun p => signedBits p.1)))
          (encodeBitList (((u,v)::ps).map (fun p => signedBits p.2))) emitted 16=
        true::pairBits (signedBits u) (encodeBitList (ps.map (fun p => signedBits p.1))) from rfl) ht hc
    refine ⟨1+t+1+c,?_,?_⟩
    · simpa [output,value,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc] using hh
    · simp only [List.length_cons]
      nlinarith

theorem output_stream_bound (scale : ℤ) (ps : List (ℤ×ℤ)) (B : ℕ)
    (hs : (signedBits scale).length≤B)
    (hp : ∀p∈ps,(signedBits p.1).length≤B ∧ (signedBits p.2).length≤B) :
    (encodeBitList ((output scale ps).map signedBits)).length≤ps.length*(8*B+20) := by
  have he := encodedWords_length_le ((output scale ps).map signedBits) (4*B+9) (by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hz
    exact output_length scale p.1 p.2 B hs (hp p hp').1 (hp p hp').2)
  simpa only [output,List.length_map,show 2*(4*B+9)+2=8*B+20 by ring] using he

theorem loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ skip_queryFree body_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralVectorCombine
