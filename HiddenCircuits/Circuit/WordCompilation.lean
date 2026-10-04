import HiddenCircuits.Circuit.ScaledWords
import HiddenCircuits.TrackTransport

namespace HiddenCircuits.Circuit

/-- Boundary projections are expanded as literal words too. -/
def closedWord {k : ℕ} (w : List (ScaledWord k)) : List (Letter (blockWidth k)) :=
  globalProjectionWord k ++ (compileProjected w).word ++ globalProjectionWord k

def closedScalar {k : ℕ} (w : List (ScaledWord k)) : ℚ :=
  (compileProjected w).scalar * ((1/64:ℚ)^(k*globalProjectionExponent k))^2

/-- A full circuit entry is one scalar times one elementary word entry, including both boundaries. -/
theorem closedWord_correct {k : ℕ} (w : List (ScaledWord k)) (x y : CodeBits k) :
    ((w.map ScaledWord.matrix).prod) x y = closedScalar w *
      wordMatrix (2*k) (closedWord w) (rawCode k x) (rawCode k y) := by
  rw [compileProjected_entry,globalProjection_eq_word]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,Matrix.smul_apply,smul_eq_mul,
    closedScalar,closedWord,wordMatrix_append]
  ring

 theorem closedWord_length {k : ℕ} (w : List (ScaledWord k)) :
    (closedWord w).length=(w.map (fun u => u.word.length)).sum+
      (w.length+2)*(globalProjectionWord k).length := by
  simp only [closedWord,List.length_append,compileProjected_length,Nat.add_mul]
  omega

 theorem closedWord_length_bound {k : ℕ} (w : List (ScaledWord k)) :
    (closedWord w).length≤(w.map (fun u => u.word.length)).sum+
      (w.length+2)*(40*k^3+40*k) := by
  rw [closedWord_length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (globalProjectionWord_length_bound k)) _

/-- Uniform statement of track transport at the level of actual word entries. -/
theorem wordMatrix_castTracks_entry {n m q : ℕ} (h : n=m) (w : List (Letter n)) (S T : State n q) :
    wordMatrix q (w.map (Letter.castTracks h)) (State.castTracks h S) (State.castTracks h T) =
      wordMatrix q w S T := by
  subst m
  simp only [State.castTracks_rfl]
  change wordMatrix q (w.map id) S T=wordMatrix q w S T
  rw [List.map_id]

/-- The constructed oracle instance has actual positive half filling and explicit physical boundaries. -/
def compileWordInstance {k : ℕ} (hk : 0<k) (w : List (ScaledWord k)) (x y : CodeBits k) : WordInstance where
  particles := 2*k
  positive := by omega
  source := State.castTracks (by rw [blockWidth_eq]; ring) (rawCode k x)
  target := State.castTracks (by rw [blockWidth_eq]; ring) (rawCode k y)
  word := (closedWord w).map (Letter.castTracks (by rw [blockWidth_eq]; ring))

/-- This compiler produces the actual WordEval input type, not just an abstract query polynomial. -/
theorem compileWordInstance_correct {k : ℕ} (hk : 0<k) (w : List (ScaledWord k)) (x y : CodeBits k) :
    ((w.map ScaledWord.matrix).prod) x y = closedScalar w * (compileWordInstance hk w x y).value := by
  rw [closedWord_correct]
  congr 1
  change _ = wordMatrix (2*k) ((closedWord w).map (Letter.castTracks _))
    (State.castTracks _ (rawCode k x)) (State.castTracks _ (rawCode k y))
  exact (wordMatrix_castTracks_entry _ _ _ _).symm

 theorem compileWordInstance_length {k : ℕ} (hk : 0<k) (w : List (ScaledWord k)) (x y : CodeBits k) :
    (compileWordInstance hk w x y).word.length=(w.map (fun u => u.word.length)).sum+
      (w.length+2)*20*k*(2*k*(k-1)+2) := by
  simp only [compileWordInstance,List.length_map,closedWord_length,globalProjectionWord_length]
  ring

end HiddenCircuits.Circuit
