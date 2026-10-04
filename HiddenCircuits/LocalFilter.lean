import HiddenCircuits.Transfers

namespace HiddenCircuits

/-- The paper's four-track filter word, with all operations still defined via permanents. -/
def filterZ : List (Letter 4) :=
  [⟨.R,1⟩, ⟨.D,2⟩, ⟨.R,2⟩, ⟨.B,1⟩, ⟨.R,2⟩]

def filterJ : List (Letter 4) :=
  [⟨.R,1⟩, ⟨.R,0⟩, ⟨.E,2⟩, ⟨.D,2⟩, ⟨.R,2⟩]

def filterT : List (Letter 4) := filterZ ++ filterJ

def filterWord : List (Letter 4) := filterT ++ filterT

def localFilter (q : ℕ) : Matrix (State 4 q) (State 4 q) ℚ :=
  (1 / 64 : ℚ) • wordMatrix q filterWord

@[simp] theorem filterWord_length : filterWord.length = 20 := rfl

/-- Explicit selected subset for one particle in two tracks. -/
def twoTrackState (i : Fin 2) : State 2 1 := ⟨{i}, by simp⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem twoTrack_rise : ∀ i j : Fin 2,
    rise 2 1 0 (twoTrackState i) (twoTrackState j) = if j = 0 then 1 else 0 := by
  decide +kernel

end HiddenCircuits
