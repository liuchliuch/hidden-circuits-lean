import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionScan

/-! A real finite clock repeats full physical coordinate scans. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck UnitCoordinateExtraction

noncomputable def rounds : OracleBlock 22 := whilePop 12 scanProgram scanProgram

lemma rounds_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (f : Frame) (hn : f.n=n) (hp : f.payload=G.bits) (x z : Coordinates n)
    (ls : List (Fin n)) (hd : ls.Nodup) (hl : ls.length≤n) (hf : f.order=labelBits ls)
    (he : f.outer=[]) (hi : f.inner=[]) (B k : ℕ) (hx : x≤z)
    (hz : ∀p∈pairs ls,pair f.D (G.edge p.1 p.2) p.1 p.2 z=z) (hB : ∀i,z i≤B) :
    ∃t,WhileExecution (12 : Fin 23) scanProgram scanProgram g
      (state {f with clock:=List.replicate k true} (encoded x) 0 0 [] [] [])
      (state {f with clock:=[]} (encoded (run f.D G.edge ls k x)) 0 0 [] [] []) t ∧
      t≤k*(scanTime n f.D B+2)+1 := by
  induction k generalizing x with
  | zero => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | succ k ih =>
    obtain ⟨c,hc,cb⟩ := scanProgram_executes g G {f with clock:=List.replicate k true}
      hn hp x z ls hd hl hf he hi B hx hz hB
    have hOut := scan_le_witness f.D G.edge ls x z hx hz
    obtain ⟨t,ht,tb⟩ := ih (scan f.D G.edge ls x) hOut
    have hclock : Function.update
        (state {f with clock:=List.replicate (k+1) true} (encoded x) 0 0 [] [] [])
        (12 : Fin 23) (List.replicate k true) =
        state {f with clock:=List.replicate k true} (encoded x) 0 0 [] [] [] := by
      funext i;fin_cases i <;> rfl
    refine ⟨1+c+1+t,?_,?_⟩
    · apply WhileExecution.one (show state {f with clock:=List.replicate (k+1) true} (encoded x) 0 0 [] [] [] 12=
        true::List.replicate k true from rfl)
      · rw [hclock];exact hc
      · exact ht
    · dsimp only at cb
      nlinarith

lemma rounds_queryFree : rounds.QueryFree := whilePop_queryFree _ _ _ scanProgram_queryFree scanProgram_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
