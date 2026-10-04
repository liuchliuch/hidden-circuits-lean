import HiddenCircuits.Approximation.FiniteCoins
import Mathlib.Data.List.OfFn

/-! Literal finite coin prefixes,
list slicing, and the exact push-forward law of the uniform finite experiment.
The proofs are independent of the mixing and sampling-to-counting modules. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.CoinLists

 def restrictTape {n m : ℕ} (h : n ≤ m) (r : CoinTape m) : CoinTape n :=
  fun i => r ⟨i.val,lt_of_lt_of_le i.isLt h⟩

 theorem restrict_ofFn {n m : ℕ} (h : n ≤ m) (r : CoinTape m) :
    List.ofFn (restrictTape h r)=(List.ofFn r).take n := by
  apply List.ext_getElem
  · simp [List.length_take,Nat.min_eq_left h]
  · intro i hi hj
    simp [restrictTape]

/-- These concrete coordinate restrictions are definitionally the two
components of `FiniteChains.splitTape`, without importing mixing theory. -/
 theorem splitTape_take (a b : ℕ) (r : CoinTape (a+b)) :
    (List.ofFn r).take a=List.ofFn (fun i : Fin a => r (i.castAdd b)) := by
  exact (restrict_ofFn (Nat.le_add_right a b) r).symm

 theorem splitTape_drop (a b : ℕ) (r : CoinTape (a+b)) :
    (List.ofFn r).drop a=List.ofFn (fun i : Fin b => r (i.natAdd a)) := by
  rw [List.ofFn_add]
  simp

private def prefixEventEquiv (a b : ℕ) (E : CoinTape a → Prop) :
    {r : CoinTape (a+b) // E (restrictTape (Nat.le_add_right a b) r)} ≃
      {r : CoinTape a // E r} × CoinTape b where
  toFun r := (⟨restrictTape (Nat.le_add_right a b) r.val,r.property⟩,
    fun i => r.val (i.natAdd a))
  invFun r := ⟨Fin.addCases r.1.val r.2,by
    have he : restrictTape (Nat.le_add_right a b) (Fin.addCases r.1.val r.2)=r.1.val := by
      funext i
      change Fin.addCases r.1.val r.2 (i.castAdd b)=r.1.val i
      simp
    rw [he]
    exact r.1.property⟩
  left_inv r := by
    apply Subtype.ext
    funext i
    refine Fin.addCases (m:=a) (n:=b) (fun j => ?_) (fun j => ?_) i
    · change Fin.addCases (restrictTape (Nat.le_add_right a b) r.val)
        (fun i => r.val (i.natAdd a)) (j.castAdd b)=r.val (j.castAdd b)
      simp only [Fin.addCases_left]
      apply congrArg r.val
      apply Fin.ext
      rfl
    · simp
  right_inv r := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      change Fin.addCases r.1.val r.2 (i.castAdd b)=r.1.val i
      simp
    · funext i
      simp

 theorem probability_restrict {n m : ℕ} (h : n ≤ m) (E : CoinTape n → Prop) :
    coinProbability m (fun r => E (restrictTape h r))=coinProbability n E := by
  classical
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le h
  unfold coinProbability
  rw [Fintype.card_congr (prefixEventEquiv n b E),Fintype.card_prod,card_coinTape,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
  have hp : (2 : ℚ)^b ≠ 0 := by positivity
  field_simp

end HiddenCircuits.Approximation.SamplerRuntime.CoinLists
