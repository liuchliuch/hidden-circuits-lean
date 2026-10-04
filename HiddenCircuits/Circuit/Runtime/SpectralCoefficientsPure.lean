import HiddenCircuits.Circuit.IntegerSpectralWeights
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime

/-! Literal ascending coefficient lists for repeated multiplication by X−a. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCoefficients
open IntegerSpectralWeights
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic

 def go (a : ℤ) : ℤ → List ℤ → List ℤ
  | prev,[] => [prev]
  | prev,c::cs => (prev-a*c)::go a c cs
 def front (a : ℤ) : ℤ → List ℤ → List ℤ
  | _,[] => []
  | prev,c::cs => (prev-a*c)::front a c cs
 def lastValue : ℤ → List ℤ → ℤ
  | prev,[] => prev
  | _,c::cs => lastValue c cs
 theorem go_eq_front (a prev : ℤ) (cs : List ℤ) : go a prev cs=front a prev cs++[lastValue prev cs] := by
  induction cs generalizing prev <;> simp_all [go,front,lastValue]
 theorem lastValue_bound (prev : ℤ) (cs : List ℤ) (B : ℕ)
    (hp : (signedBits prev).length≤B) (hc : ∀c∈cs,(signedBits c).length≤B) :
    (signedBits (lastValue prev cs)).length≤B := by
  induction cs generalizing prev with
  | nil => exact hp
  | cons c cs ih => exact ih c (hc c (by simp)) (fun z hz => hc z (by simp [hz]))
 def step (a : ℤ) (cs : List ℤ) : List ℤ := go a 0 cs
 def coefficients (xs : List ℤ) : List ℤ :=
  List.ofFn (fun i : Fin (xs.length+1) => coeffs xs i.val)
 def run (xs : List ℤ) : List ℤ := xs.foldl (fun cs a => step a cs) [1]

@[simp] theorem go_length (a prev : ℤ) (cs : List ℤ) : (go a prev cs).length=cs.length+1 := by
  induction cs generalizing prev <;> simp_all [go]
@[simp] theorem coefficients_length (xs : List ℤ) : (coefficients xs).length=xs.length+1 := by simp [coefficients]

 theorem go_get_zero (a prev : ℤ) (cs : List ℤ) : (go a prev cs).head! = prev-a*cs.head! := by
  cases cs <;> simp [go]

 theorem go_get (a prev : ℤ) (cs : List ℤ) (k : ℕ) :
    (go a prev cs)[k]?.getD 0=(if k=0 then prev else cs[k-1]?.getD 0)-a*cs[k]?.getD 0 := by
  induction cs generalizing prev k with
  | nil => cases k <;> simp [go]
  | cons c cs ih =>
    cases k with
    | zero => simp [go]
    | succ k =>
      cases k with
      | zero => simpa [go] using ih c 0
      | succ k => simpa [go] using ih c (k+1)

 theorem coefficients_get (xs : List ℤ) (k : ℕ) : (coefficients xs)[k]?.getD 0=coeffs xs k := by
  by_cases hk:k<xs.length+1
  · rw [List.getElem?_eq_getElem (by simpa using hk)]
    simp only [coefficients,List.getElem_ofFn,Option.getD_some]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
    simp [coeffs_zero xs k (by omega)]

 theorem step_coefficients (a : ℤ) (xs : List ℤ) : step a (coefficients xs)=coefficients (a::xs) := by
  apply List.ext_getElem
  · simp [step]
  · intro k hk hk'
    have h₁ := go_get a 0 (coefficients xs) k
    have h₂ := coefficients_get (a::xs) k
    rw [List.getElem?_eq_getElem (show k<(go a 0 (coefficients xs)).length from hk)] at h₁
    rw [List.getElem?_eq_getElem hk'] at h₂
    simp only [Option.getD_some] at h₁ h₂
    dsimp only [step]
    rw [h₁,h₂,coefficients_get,coefficients_get]
    cases k <;> simp [coeffs] <;> ring

 theorem coefficients_reverse (xs : List ℤ) : coefficients xs.reverse=coefficients xs := by
  have hp : poly xs.reverse=poly xs := by simp [poly,List.map_reverse,List.prod_reverse]
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have h₁ := coefficients_get xs.reverse k
    have h₂ := coefficients_get xs k
    rw [List.getElem?_eq_getElem hk] at h₁
    rw [List.getElem?_eq_getElem hk'] at h₂
    simp only [Option.getD_some,coeffs_eq,hp] at h₁ h₂
    exact h₁.trans h₂.symm

 theorem fold_coefficients (ys xs : List ℤ) :
    ys.foldl (fun cs a => step a cs) (coefficients xs)=coefficients (ys.reverse++xs) := by
  induction ys generalizing xs with
  | nil => simp
  | cons a ys ih =>
    simp only [List.foldl_cons,step_coefficients,ih,List.reverse_cons]
    simp [List.append_assoc]

 theorem run_correct (xs : List ℤ) : run xs=coefficients xs := by
  have he : coefficients []=[1] := rfl
  simpa [run,he,coefficients_reverse] using fold_coefficients xs []

 theorem coefficients_bit_bound (xs : List ℤ) (b : ℕ) (hxs : ∀ a∈xs,a.natAbs≤2^b)
    (c : ℤ) (hc : c∈coefficients xs) : (signedBits c).length≤(b+1)*xs.length+2 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  simpa [signedBits,encodeNat_length] using coeffs_bit_bound xs b hxs i.val

 theorem go_bound (a prev : ℤ) (cs : List ℤ) (A B : ℕ) (ha:a.natAbs≤A)
    (hp:prev.natAbs≤B) (hc:∀c∈cs,c.natAbs≤B) : ∀c∈go a prev cs,c.natAbs≤B+A*B := by
  induction cs generalizing prev with
  | nil => simpa [go] using hp.trans (Nat.le_add_right _ _)
  | cons c cs ih =>
    have hcm := hc c (by simp)
    have hh : (prev-a*c).natAbs≤B+A*B := by
      apply (Int.natAbs_sub_le prev (a*c)).trans
      rw [Int.natAbs_mul]
      exact Nat.add_le_add hp (Nat.mul_le_mul ha hcm)
    intro z hz
    simp only [go,List.mem_cons] at hz
    rcases hz with rfl|hz
    · exact hh
    · exact ih c hcm (fun z hz => hc z (by simp [hz])) z hz
end HiddenCircuits.Circuit.Runtime.SpectralCoefficients
