import HiddenCircuits.Complexity.CNFEncoding

/-! Literal and clause width bounds for the actual binary CNF encoding. -/
namespace HiddenCircuits.Complexity

lemma list_sum_map_le {α : Type*} (xs : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ a ∈ xs, f a ≤ B) : (xs.map f).sum ≤ B*xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

namespace CNF
variable {n m : ℕ}

@[simp] theorem literalBits_length (l : Fin n × Bool) : (literalBits l).length = 2*l.1.val+2 := by
  simp [literalBits]

theorem literalBits_length_le (l : Fin n × Bool) : (literalBits l).length ≤ 2*n := by
  rw [literalBits_length]
  have := l.1.isLt
  omega

theorem clauseBits_length_le (c : List (Fin n × Bool)) (W : ℕ) (hc : c.length ≤ W) :
    (clauseBits c).length ≤ (4*n+2)*W := by
  have h := list_sum_map_le c (fun l => (literalBits l).length) (2*n) (fun l _ => literalBits_length_le l)
  simp only [clauseBits,encodeBitList_length,List.map_map,List.length_map,Function.comp_def]
  have hh : (4*n+2)*c.length ≤ (4*n+2)*W := Nat.mul_le_mul_left _ hc
  nlinarith

/-- Polynomial binary size in variables, clauses, and the actual maximum clause width. -/
theorem bits_length_le (F : CNF n m) (W : ℕ) (hW : ∀ k, (F.clause k).length ≤ W) :
    F.bits.length ≤ 10*(n+1)*(W+1)*(m+1) := by
  have h := list_sum_map_le (List.ofFn F.clause) (fun c => (clauseBits c).length) ((4*n+2)*W) (by
    intro c hc
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
    exact clauseBits_length_le _ W (hW k))
  simp only [List.length_ofFn] at h
  simp only [bits,pairBits_length,List.length_replicate,encodeBitList_length,List.length_map,
    List.length_ofFn,List.map_map,Function.comp_def]
  nlinarith [Nat.zero_le (n*W*m),Nat.zero_le (n*m),Nat.zero_le (n*W),Nat.zero_le (W*m)]

end CNF
end HiddenCircuits.Complexity
