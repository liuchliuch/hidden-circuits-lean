import HiddenCircuits.Circuit.SpectralRecovery

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- A finite word with arbitrarily interleaved constant gates and marked three-eigenvalue diagonal gates. -/
inductive SpectralGate (ι : Type*) where
  | fixed (M : Matrix ι ι ℚ)
  | marked (classify : ι → Fin 3)

def markCount {ι : Type*} : List (SpectralGate ι) → ℕ
  | [] => 0
  | .fixed _ :: w => markCount w
  | .marked _ :: w => markCount w+1

def firstCount {ι : Type*} : (w : List (SpectralGate ι)) → ι → StatePath ι w.length → ℕ
  | [],_,_ => 0
  | .fixed _::w,s,p => firstCount w p.1 p.2
  | .marked c::w,s,p => firstCount w p.1 p.2 + if c s=0 then 1 else 0

def secondCount {ι : Type*} : (w : List (SpectralGate ι)) → ι → StatePath ι w.length → ℕ
  | [],_,_ => 0
  | .fixed _::w,s,p => secondCount w p.1 p.2
  | .marked c::w,s,p => secondCount w p.1 p.2 + if c s=1 then 1 else 0

theorem class_flags_le (c : Fin 3) : (if c=0 then 1 else 0) + (if c=1 then 1 else 0) ≤ (1:ℕ) := by
  fin_cases c <;> decide

 theorem counts_le_marks {ι : Type*} (w : List (SpectralGate ι)) (s : ι) (p : StatePath ι w.length) :
    firstCount w s p+secondCount w s p≤markCount w := by
  induction w generalizing s with
  | nil => rfl
  | cons g w ih =>
    have ht := ih p.1 p.2
    cases g with
    | fixed M => exact ht
    | marked c =>
      simp only [firstCount,secondCount,markCount]
      have hc := class_flags_le (c s)
      omega

/-- The actual finite class of a path's two spectral multiplicities. -/
def pathSpectralIndex {ι : Type*} (w : List (SpectralGate ι)) (s : ι) (p : StatePath ι w.length) :
    SpectralIndex (markCount w) :=
  ⟨⟨firstCount w s p,by have h := counts_le_marks w s p; omega⟩,
    ⟨secondCount w s p,by
      change secondCount w s p < markCount w-firstCount w s p+1
      have h := counts_le_marks w s p
      omega⟩⟩

section
variable {ι : Type*} [DecidableEq ι]

/-- Diagonal zeroes remain in the weight; no impossible state path contributes. -/
def basePathWeight : (w : List (SpectralGate ι)) → ι → StatePath ι w.length → ℚ
  | [],_,_ => 1
  | .fixed M::w,s,p => M s p.1 * basePathWeight w p.1 p.2
  | .marked _::w,s,p => (if s=p.1 then 1 else 0) * basePathWeight w p.1 p.2

/-- The actual shared even-power sample: the diagonal values are4^r,9^r,1. -/
def SpectralGate.sample (r : ℕ) : SpectralGate ι → Matrix ι ι ℚ
  | .fixed M => M
  | .marked c => Matrix.diagonal (fun s => if c s=0 then (4:ℚ)^r else if c s=1 then (9:ℚ)^r else 1)

/-- Target diagonal1,1,z simultaneously covers N at z=0 and CZ at z=−1. -/
def SpectralGate.target (z : ℚ) : SpectralGate ι → Matrix ι ι ℚ
  | .fixed M => M
  | .marked c => Matrix.diagonal (fun s => if c s=0 ∨ c s=1 then 1 else z)

/-- Actual ordered product along a successive-state path. -/
def gatePathWeight (value : SpectralGate ι → Matrix ι ι ℚ) :
    (w : List (SpectralGate ι)) → ι → StatePath ι w.length → ℚ
  | [],_,_ => 1
  | g::w,s,p => value g s p.1 * gatePathWeight value w p.1 p.2

theorem sample_eigen_factor (c : Fin 3) (r : ℕ) :
    (if c=0 then (4:ℚ)^r else if c=1 then (9:ℚ)^r else 1) =
      ((4:ℚ)^(if c=0 then 1 else 0) * (9:ℚ)^(if c=1 then 1 else 0))^r := by
  fin_cases c <;> simp

 theorem target_eigen_factor (c : Fin 3) (z : ℚ) :
    (if c=0 ∨ c=1 then (1:ℚ) else z) = z^(1-(if c=0 then 1 else 0)-(if c=1 then 1 else 0)) := by
  fin_cases c <;> simp

 theorem sample_path_weight (w : List (SpectralGate ι)) (r : ℕ) (s : ι) (p : StatePath ι w.length) :
    gatePathWeight (SpectralGate.sample r) w s p = basePathWeight w s p *
      ((4:ℚ)^firstCount w s p * (9:ℚ)^secondCount w s p)^r := by
  induction w generalizing s with
  | nil => simp [gatePathWeight,basePathWeight,firstCount,secondCount]
  | cons g w ih =>
    cases g with
    | fixed M =>
      simp only [gatePathWeight,SpectralGate.sample,basePathWeight,firstCount,secondCount,ih]
      ring
    | marked c =>
      simp only [gatePathWeight,SpectralGate.sample,Matrix.diagonal_apply,basePathWeight,firstCount,secondCount,ih]
      by_cases he:s=p.1
      · rw [if_pos he,if_pos he,sample_eigen_factor]
        simp only [one_mul,pow_add,mul_pow]
        ring
      · simp [he]

 theorem target_path_weight (w : List (SpectralGate ι)) (z : ℚ) (s : ι) (p : StatePath ι w.length) :
    gatePathWeight (SpectralGate.target z) w s p = basePathWeight w s p *
      z^(markCount w-firstCount w s p-secondCount w s p) := by
  induction w generalizing s with
  | nil => simp [gatePathWeight,basePathWeight,firstCount,secondCount,markCount]
  | cons g w ih =>
    cases g with
    | fixed M =>
      simp only [gatePathWeight,SpectralGate.target,basePathWeight,firstCount,secondCount,markCount,ih]
      ring
    | marked c =>
      have hb := counts_le_marks w p.1 p.2
      have hc := class_flags_le (c s)
      simp only [gatePathWeight,SpectralGate.target,Matrix.diagonal_apply,basePathWeight,firstCount,secondCount,markCount,ih]
      by_cases he:s=p.1
      · rw [if_pos he,if_pos he,target_eigen_factor]
        have hexp : markCount w+1-(firstCount w p.1 p.2 + if c s=0 then 1 else 0)-
            (secondCount w p.1 p.2 + if c s=1 then 1 else 0) =
            (markCount w-firstCount w p.1 p.2-secondCount w p.1 p.2)+
              (1-(if c s=0 then 1 else 0)-(if c s=1 then 1 else 0)) := by omega
        rw [hexp,pow_add]
        ring
      · simp [he]

end
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ordered circuit multiplication is the actual finite sum of its gate-path products. -/
theorem gate_product_paths (w : List (SpectralGate ι)) (value : SpectralGate ι → Matrix ι ι ℚ)
    (s t : ι) : (w.map value).prod s t = ∑ p : StatePath ι w.length,
      if pathEnd w.length s p=t then gatePathWeight value w s p else 0 := by
  induction w generalizing s with
  | nil =>
    change (1 : Matrix ι ι ℚ) s t = ∑ p : PUnit, if s=t then 1 else 0
    simp [Matrix.one_apply]
  | cons g w ih =>
    rw [List.map_cons,List.prod_cons,Matrix.mul_apply]
    change (∑ j, value g s j*(w.map value).prod j t)=
      ∑ p : ι × StatePath ι w.length,
        if pathEnd w.length p.1 p.2=t then value g s p.1*gatePathWeight value w p.1 p.2 else 0
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih j,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp

/-- Exact recovery of all marked diagonal constraints in an arbitrary actual matrix circuit.
The finite path counts and their coefficient grouping are constructed above, not assumed. -/
theorem spectral_circuit_recovery (w : List (SpectralGate ι)) (z : ℚ) (s t : ι) :
    (∑ r ∈ Finset.range (Fintype.card (SpectralIndex (markCount w))),
      spectralCoefficient (markCount w)
        (fun x => z^(markCount w-x.1.val-x.2.val)) r *
      (w.map (SpectralGate.sample r)).prod s t) =
      (w.map (SpectralGate.target z)).prod s t := by
  let weight : StatePath ι w.length → ℚ := fun p =>
    if pathEnd w.length s p=t then basePathWeight w s p else 0
  have hs (r : ℕ) : (w.map (SpectralGate.sample r)).prod s t =
      ∑ p : StatePath ι w.length, weight p*rationalSpectralNode (pathSpectralIndex w s p)^r := by
    rw [gate_product_paths]
    apply Finset.sum_congr rfl
    intro p _
    rw [sample_path_weight]
    simp only [rationalSpectralNode,pathSpectralIndex,spectralNode,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,weight]
    split_ifs <;> simp
  have ht : (w.map (SpectralGate.target z)).prod s t =
      ∑ p : StatePath ι w.length, weight p * z^(markCount w-(pathSpectralIndex w s p).1.val-(pathSpectralIndex w s p).2.val) := by
    rw [gate_product_paths]
    apply Finset.sum_congr rfl
    intro p _
    rw [target_path_weight]
    simp only [pathSpectralIndex,weight]
    split_ifs <;> simp
  simp_rw [hs]
  rw [ht]
  exact spectral_path_recovery (markCount w) (pathSpectralIndex w s) weight _

end
end HiddenCircuits.Circuit
