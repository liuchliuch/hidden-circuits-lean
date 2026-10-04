import HiddenCircuits.GraphReduction.UnitIntervalGeometry
import HiddenCircuits.GraphReduction.CliqueProbeGraph

/-! A literal common-length interval representation of the clique-probe query graph. -/
namespace HiddenCircuits.GraphReduction
namespace UnitInterval
variable {V I : Type*}

/-- Rational left endpoints and one common positive interval length. -/
structure Representation (G : SimpleGraph V) where
  length : ℚ
  positive : 0 < length
  left : V → ℚ
  adjacency : ∀ x y, G.Adj x y ↔ x≠y ∧
    (Set.Icc (left x) (left x+length) ∩ Set.Icc (left y) (left y+length)).Nonempty

def probeLeft (Λ : ℚ) (layer : V → ℤ) (offset : V → ℚ) (index : I → ℤ)
    {s : ℕ} : V ⊕ (I × Fin s) → ℚ
  | .inl v => (layer v:ℚ)*Λ+offset v
  | .inr (i,_) => ((2*index i+1:ℤ):ℚ)*Λ

private theorem original_interval (Λ : ℚ) (j : ℤ) (a : ℚ) :
    Set.Icc ((j:ℚ)*Λ+a) ((j:ℚ)*Λ+a+Λ)=interval Λ j a := by
  unfold interval
  congr 1 <;> ring
private theorem probe_interval (Λ : ℚ) (j : ℤ) :
    Set.Icc (((2*j+1:ℤ):ℚ)*Λ) ((((2*j+1:ℤ):ℚ)*Λ)+Λ)=probe Λ j := by
  unfold probe
  congr 1
  push_cast
  ring

/-- Exact graph equality, including all identical probe copies and unequal classes. -/
theorem probeLeft_adj {G : SimpleGraph V} {Λ : ℚ} (hΛ : 0<Λ)
    (layer : V → ℤ) (offset : V → ℚ) (index : I → ℤ)
    (hinj : Function.Injective index) (hoff : ∀ v, 0<offset v ∧ offset v<Λ)
    (hG : ∀ v w, G.Adj v w ↔ v≠w ∧
      (interval Λ (layer v) (offset v) ∩ interval Λ (layer w) (offset w)).Nonempty)
    (s : ℕ) (x y : V ⊕ (I × Fin s)) :
    (cliqueProbeGraph G (fun i v => layer v=2*index i ∨ layer v=2*index i+1) s).Adj x y ↔
      x≠y ∧ (Set.Icc (probeLeft Λ layer offset index x) (probeLeft Λ layer offset index x+Λ) ∩
        Set.Icc (probeLeft Λ layer offset index y) (probeLeft Λ layer offset index y+Λ)).Nonempty := by
  rcases x with v|⟨i,a⟩ <;> rcases y with w|⟨k,b⟩
  · simpa only [cliqueProbeGraph,probeLeft,original_interval,ne_eq,Sum.inl.injEq] using hG v w
  · simp only [cliqueProbeGraph,probeLeft,original_interval,probe_interval,ne_eq,
      Sum.inl_ne_inr,not_false_eq_true,true_and]
    rw [Set.inter_comm,probe_original hΛ (hoff v).1 (hoff v).2]
  · simp only [cliqueProbeGraph,probeLeft,original_interval,probe_interval,ne_eq,
      Sum.inr_ne_inl,not_false_eq_true,true_and]
    rw [probe_original hΛ (hoff w).1 (hoff w).2]
  · simp only [cliqueProbeGraph,probeLeft,probe_interval,ne_eq,Sum.inr.injEq,Prod.mk.injEq]
    by_cases hik : i=k
    · subst k
      have hp : (probe Λ (index i)).Nonempty := by simpa using probe_self hΛ (index i)
      simp [hp]
    · have hh := probes_separated hΛ (fun he => hik (hinj he))
      simp [hik,hh]

def cliqueProbeRepresentation {G : SimpleGraph V} {Λ : ℚ} (hΛ : 0<Λ)
    (layer : V → ℤ) (offset : V → ℚ) (index : I → ℤ)
    (hinj : Function.Injective index) (hoff : ∀ v, 0<offset v ∧ offset v<Λ)
    (hG : ∀ v w, G.Adj v w ↔ v≠w ∧
      (interval Λ (layer v) (offset v) ∩ interval Λ (layer w) (offset w)).Nonempty)
    (s : ℕ) : Representation
      (cliqueProbeGraph G (fun i v => layer v=2*index i ∨ layer v=2*index i+1) s) where
  length := Λ
  positive := hΛ
  left := probeLeft Λ layer offset index
  adjacency := probeLeft_adj hΛ layer offset index hinj hoff hG s


/-- All generated endpoints have an explicit magnitude bound, independent of probe multiplicity. -/
theorem probeLeft_bounds {Λ : ℚ} (hΛ : 0<Λ)
    (layer : V → ℤ) (offset : V → ℚ) (index : I → ℤ) (h : ℕ)
    (hl : ∀ v, 0≤layer v ∧ layer v≤2*(h:ℤ))
    (ho : ∀ v, 0<offset v ∧ offset v<Λ)
    (hi : ∀ i, 0 ≤ index i ∧ index i≤(h:ℤ))
    {s : ℕ} (x : V ⊕ (I × Fin s)) :
    0≤probeLeft Λ layer offset index x ∧
      probeLeft Λ layer offset index x+Λ≤(2*(h:ℚ)+2)*Λ := by
  rcases x with v|⟨i,j⟩
  · change 0≤(layer v:ℚ)*Λ+offset v ∧ _
    have h0 : (0:ℚ)≤(layer v:ℚ) := by exact_mod_cast (hl v).1
    have h1 : (layer v:ℚ)≤2*(h:ℚ) := by exact_mod_cast (hl v).2
    have hm0 := mul_nonneg h0 hΛ.le
    have hm1 := mul_le_mul_of_nonneg_right h1 hΛ.le
    dsimp [probeLeft]
    constructor <;> nlinarith [(ho v).1,(ho v).2]
  · dsimp [probeLeft]
    have h0 : (0:ℚ)≤(index i:ℚ) := by exact_mod_cast (hi i).1
    have h1 : (index i:ℚ)≤(h:ℚ) := by exact_mod_cast (hi i).2
    have hm0 := mul_nonneg h0 hΛ.le
    have hm1 := mul_le_mul_of_nonneg_right h1 hΛ.le
    push_cast
    constructor <;> nlinarith


/-- Scaling the explicit rational coordinates gives literally unit-length intervals. -/
def Representation.unitLength {G : SimpleGraph V} (r : Representation G) : Representation G where
  length := 1
  positive := by norm_num
  left := fun v => r.left v / r.length
  adjacency := by
    intro x y
    rw [r.adjacency]
    apply and_congr_right
    intro _
    rw [icc_overlap (by linarith [r.positive]) (by linarith [r.positive]),
      icc_overlap (by linarith) (by linarith)]
    have hx : r.left x/r.length+1=(r.left x+r.length)/r.length := by
      rw [add_div,div_self (ne_of_gt r.positive)]
    have hy : r.left y/r.length+1=(r.left y+r.length)/r.length := by
      rw [add_div,div_self (ne_of_gt r.positive)]
    rw [hx,hy,div_le_div_iff_of_pos_right r.positive,div_le_div_iff_of_pos_right r.positive]

end UnitInterval
end HiddenCircuits.GraphReduction
