import HiddenCircuits.GraphReduction.MonotoneDiagram

/-! Exact upper and lower endpoint blocks for private clique probes. -/
namespace HiddenCircuits.GraphReduction
namespace PrivateProbe

/-- Interleave the two original layers between their two private probe classes. -/
def reorder (n s : ℕ) : BlockContent n s ≃ BlockContent n s where
  toFun
    | .inl x => .inl x
    | .inr (.inl q) => .inr (.inr q)
    | .inr (.inr q) => .inr (.inl q)
  invFun
    | .inl x => .inl x
    | .inr (.inl q) => .inr (.inr q)
    | .inr (.inr q) => .inr (.inl q)
  left_inv := by intro x; rcases x with (x|(q|q)) <;> rfl
  right_inv := by intro x; rcases x with (x|(q|q)) <;> rfl

def top {n : ℕ} (m : InterleaveMode n) (s : ℕ) : BlockContent n s ↪ Fin (endpointBlockWidth n s) :=
  (reorder n s).toEmbedding.trans (lowerBlock m s)

/-- Reversing the whole block produces increasing track order and reverses each probe clique. -/
def bottom {n : ℕ} (m : InterleaveMode n) (s : ℕ) : BlockContent n s ↪ Fin (endpointBlockWidth n s) :=
  (top m s).trans ⟨Fin.rev,Fin.rev_injective⟩

@[simp] theorem top_even {n s : ℕ} (m : InterleaveMode n) (u : Fin n) :
    (top m s (.inl (.inl u))).val=s+m.evenOffset u := rfl
@[simp] theorem top_odd {n s : ℕ} (m : InterleaveMode n) (u : Fin n) :
    (top m s (.inl (.inr u))).val=s+m.oddOffset u := rfl
@[simp] theorem top_evenProbe {n s : ℕ} (m : InterleaveMode n) (u : Fin s) :
    (top m s (.inr (.inl u))).val=u.val := rfl
@[simp] theorem top_oddProbe {n s : ℕ} (m : InterleaveMode n) (u : Fin s) :
    (top m s (.inr (.inr u))).val=s+(2*n+u.val) := rfl
@[simp] theorem bottom_even {n s : ℕ} (m : InterleaveMode n) (u : Fin n) :
    (bottom m s (.inl (.inl u))).val=s+(2*n-1-m.evenOffset u) := by
  change (Fin.rev (top m s (.inl (.inl u)))).val=_
  rw [Fin.val_rev,top_even]
  have := m.evenOffset_lt u
  unfold endpointBlockWidth
  omega
@[simp] theorem bottom_odd {n s : ℕ} (m : InterleaveMode n) (u : Fin n) :
    (bottom m s (.inl (.inr u))).val=s+(2*n-1-m.oddOffset u) := by
  change (Fin.rev (top m s (.inl (.inr u)))).val=_
  rw [Fin.val_rev,top_odd]
  have := m.oddOffset_lt u
  unfold endpointBlockWidth
  omega
@[simp] theorem bottom_evenProbe {n s : ℕ} (m : InterleaveMode n) (u : Fin s) :
    (bottom m s (.inr (.inl u))).val=s+2*n+(s-1-u.val) := by
  change (Fin.rev (top m s (.inr (.inl u)))).val=_
  rw [Fin.val_rev,top_evenProbe]
  unfold endpointBlockWidth
  omega
@[simp] theorem bottom_oddProbe {n s : ℕ} (m : InterleaveMode n) (u : Fin s) :
    (bottom m s (.inr (.inr u))).val=s-1-u.val := by
  change (Fin.rev (top m s (.inr (.inr u)))).val=_
  rw [Fin.val_rev,top_oddProbe]
  unfold endpointBlockWidth
  omega

 theorem top_even_lt_iff {n s : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    (top m s (.inl (.inl u))).val < (top m s (.inl (.inl v))).val ↔ v.val<u.val := by
  simp [m.evenOffset_lt_iff]
 theorem top_odd_lt_iff {n s : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    (top m s (.inl (.inr u))).val < (top m s (.inl (.inr v))).val ↔ v.val<u.val := by
  simp [m.oddOffset_lt_iff]
 theorem bottom_even_lt_iff {n s : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    (bottom m s (.inl (.inl u))).val < (bottom m s (.inl (.inl v))).val ↔ u.val<v.val := by
  change Fin.rev (top m s (.inl (.inl u))) < Fin.rev (top m s (.inl (.inl v))) ↔ _
  rw [Fin.rev_lt_rev]
  exact top_even_lt_iff m v u
 theorem bottom_odd_lt_iff {n s : ℕ} (m : InterleaveMode n) (u v : Fin n) :
    (bottom m s (.inl (.inr u))).val < (bottom m s (.inl (.inr v))).val ↔ u.val<v.val := by
  change Fin.rev (top m s (.inl (.inr u))) < Fin.rev (top m s (.inl (.inr v))) ↔ _
  rw [Fin.rev_lt_rev]
  exact top_odd_lt_iff m v u

 theorem top_cut {p s : ℕ} (P : CutPair p) (u v : Fin (2*p)) :
    (top P.upperMode s (.inl (.inr v))).val < (top P.upperMode s (.inl (.inl u))).val ↔
      P.first u v=1 := by simp [P.upper_interleave_cut]
 theorem bottom_cut {p s : ℕ} (P : CutPair p) (u v : Fin (2*p)) :
    (bottom P.lowerMode s (.inl (.inl v))).val < (bottom P.lowerMode s (.inl (.inr u))).val ↔
      P.second u v=1 := by
  change Fin.rev (top P.lowerMode s (.inl (.inl v))) < Fin.rev (top P.lowerMode s (.inl (.inr u))) ↔ _
  rw [Fin.rev_lt_rev]
  change s+P.lowerMode.oddOffset u<s+P.lowerMode.evenOffset v ↔ _
  rw [Nat.add_lt_add_iff_left,InterleaveMode.odd_lt_even_matrix,CutPair.lowerMode_matrix]
  rfl

end PrivateProbe
end HiddenCircuits.GraphReduction
