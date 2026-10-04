import HiddenCircuits.Approximation.CanonicalPaths.MountainIntervals

/-! Fresh indexed-side incidence: each interior path vertex pairs its two ports. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.MountainSide
variable {m : ℕ}
abbrev Port (m : ℕ) := Fin m × Bool

def node (p : Port m) : Fin (m+1) := if p.2 then p.1.succ else p.1.castSucc

def mate (p : Port m) : Port m :=
  if p.2 then
    if h : p.1.val+1 < m then (⟨p.1.val+1,h⟩,false) else p
  else
    if h : 0 < p.1.val then (⟨p.1.val-1,by have := p.1.isLt; omega⟩,true) else p

theorem mate_node (p : Port m) : node (mate p)=node p := by
  rcases p with ⟨i,b⟩
  cases b
  · by_cases h : 0 < i.val
    · simp only [mate,Bool.false_eq_true,↓reduceIte,dif_pos h,node]
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_castSucc]
      omega
    · simp [mate,h]
  · by_cases h : i.val+1 < m
    · simp only [mate,↓reduceIte,dif_pos h,node,Bool.false_eq_true]
      rfl
    · simp [mate,h]

theorem mate_involutive : Function.Involutive (mate (m:=m)) := by
  rintro ⟨i,b⟩
  cases b
  · by_cases h : 0 < i.val
    · have hi : i.val-1+1 < m := by have := i.isLt; omega
      have he : i.val-1+1=i.val := by omega
      simp [mate,h,hi,he]
    · simp [mate,h]
  · by_cases h : i.val+1 < m
    · simp [mate,h]
    · simp [mate,h]

theorem mate_fixed_iff (p : Port m) : mate p=p ↔ (node p).val=0 ∨ (node p).val=m := by
  rcases p with ⟨i,b⟩
  have hi := i.isLt
  cases b
  · by_cases h : 0 < i.val
    · simp [mate,node,h]
      omega
    · simp [mate,node,h]
      omega
  · by_cases h : i.val+1 < m
    · simp [mate,node,h]
      omega
    · simp [mate,node,h]
      omega

/-- A change to the other incidence port stays on an adjacent path edge. -/
theorem mate_edge_distance (p : Port m) :
    (mate p).1.val ≤ p.1.val+1 ∧ p.1.val ≤ (mate p).1.val+1 := by
  rcases p with ⟨i,b⟩
  cases b <;> simp only [mate,Bool.false_eq_true,↓reduceIte]
  all_goals split_ifs <;> simp only [Prod.fst] <;> omega


def bottomPort (hm : 0 < m) : Port m := (⟨0,hm⟩,false)
def topPort (hm : 0 < m) : Port m := (⟨m-1,by omega⟩,true)

theorem node_zero_iff (hm : 0 < m) (p : Port m) : (node p).val=0 ↔ p=bottomPort hm := by
  rcases p with ⟨i,b⟩
  cases b
  · simp [node,bottomPort,Fin.ext_iff]
  · simp [node,bottomPort]

theorem node_last_iff (hm : 0 < m) (p : Port m) : (node p).val=m ↔ p=topPort hm := by
  rcases p with ⟨i,b⟩
  have hi := i.isLt
  cases b
  · simp [node,topPort]
    omega
  · simp [node,topPort,Fin.ext_iff]
    omega

end HiddenCircuits.Approximation.CanonicalPaths.MountainSide
