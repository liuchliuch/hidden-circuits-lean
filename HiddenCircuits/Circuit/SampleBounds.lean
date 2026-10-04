import HiddenCircuits.Circuit.SampleWords

namespace HiddenCircuits.Circuit

 theorem availableGate_length_sum {n : ℕ} (w : List (AvailableGate n)) :
    (w.map (fun g => g.compile.word.length)).sum≤88*w.length := by
  induction w with
  | nil => simp
  | cons g w ih =>
    have hg := g.compile_length
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- All inserted local projections are accounted for in a linear-in-u physical word bound. -/
theorem sampleGWord_length (u : ℕ) : (sampleGWord u).word.length≤1312*u+1640 := by
  have h := availableGate_length_sum (sampleLocalCircuit u)
  rw [sampleLocalCircuit_length] at h
  change (compileProjected ((sampleLocalCircuit u).map AvailableGate.compile)).word.length≤_
  rw [compileProjected_length]
  simp only [List.map_map,Function.comp_def,List.length_map,sampleLocalCircuit_length]
  have hp : (globalProjectionWord 2).length=240 := by rw [globalProjectionWord_length]
  rw [hp]
  nlinarith

 theorem DeltaGate.compileSample_length {n : ℕ} (g : DeltaGate n) (u : ℕ) :
    (g.compileSample u).word.length≤1312*u+1640 := by
  cases g with
  | one p g =>
    have h := oneGateWord_length g
    simpa only [compileSample,placedOneGateWord,ScaledWord.lift_length] using
      h.trans (by omega : 88≤1312*u+1640)
  | constraint p => simpa only [compileSample,ScaledWord.lift_length] using sampleGWord_length u

 theorem deltaOccurrences_le_length {n : ℕ} (w : List (DeltaGate n)) : deltaOccurrences w≤w.length := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g <;> simp only [deltaOccurrences,List.map_cons,List.sum_cons,DeltaGate.mark,List.length_cons] at * <;> omega

/-- The polynomial physical-query bound with the actual number of sampled occurrences. -/
theorem deltaQuery_word_length {n : ℕ} (hn : 0<n) (w : List (DeltaGate n)) (u : ℕ) (x y : CodeBits n) :
    (compileWordInstance hn (w.map (DeltaGate.compileSample u)) x y).word.length ≤
      (1312*u+1640)*w.length + (w.length+2)*(40*n^3+40*n) := by
  have hs : ((w.map (DeltaGate.compileSample u)).map (fun a => a.word.length)).sum ≤ (1312*u+1640)*w.length := by
    induction w with
    | nil => simp
    | cons g w ih =>
      have hg := g.compileSample_length u
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  change ((closedWord (w.map (DeltaGate.compileSample u))).map (Letter.castTracks _)).length≤_
  rw [List.length_map]
  exact (closedWord_length_bound _).trans (by simp only [List.length_map]; omega)

/-- At the actual interpolation nodes u≤2h, every emitted query has polynomial length in n+|circuit|. -/
theorem deltaQuery_word_length_nodes {n : ℕ} (hn : 0<n) (w : List (DeltaGate n))
    (u : Fin (2*deltaOccurrences w+1)) (x y : CodeBits n) :
    (compileWordInstance hn (w.map (DeltaGate.compileSample u.val)) x y).word.length ≤
      (2624*w.length+1640)*w.length + (w.length+2)*(40*n^3+40*n) := by
  have hu := u.isLt
  have hh := deltaOccurrences_le_length w
  have hb : 1312*u.val+1640≤2624*w.length+1640 := by omega
  exact (deltaQuery_word_length hn w u.val x y).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right w.length hb) _)

/-- No unavailable zero-bit gate or zero-particle WordEval instance is needed. -/
instance : IsEmpty (DeltaGate 0) := ⟨by
  intro g
  cases g with
  | one p _ => have h := p.size; omega
  | constraint p => have h := p.size; omega⟩

 theorem zero_bit_circuit_empty (w : List (DeltaGate 0)) : w=[] := by
  cases w with
  | nil => rfl
  | cons g _ => exact isEmptyElim g

end HiddenCircuits.Circuit
