import HiddenCircuits.Complexity.GraphEncoding

/-! Soundness of accepted binary encodings, including malformed-input handling. -/
namespace HiddenCircuits.Complexity

theorem pairBits_of_unpair : ∀ (s x y : BitString),
    unpairBits s = some (x,y) → pairBits x y = s
  | [], x, y, h => by simp [unpairBits] at h
  | false::s, x, y, h => by
    simp only [unpairBits,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  | true::[], x, y, h => by simp [unpairBits] at h
  | true::b::s, x, y, h => by
    cases hs : unpairBits s with
    | none => simp [unpairBits,hs] at h
    | some xy =>
      rcases xy with ⟨a,c⟩
      simp only [unpairBits,hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact congrArg (fun z => true::b::z) (pairBits_of_unpair s a c hs)

lemma unpairBits_length {s x y : BitString} (h : unpairBits s = some (x,y)) :
    s.length = 2*x.length+y.length+1 := by
  rw [← pairBits_of_unpair s x y h,pairBits_length]

namespace GraphInput

/-- Every accepted graph header fits inside the actual input string. -/
theorem decode_vertices_bound {x : BitString} {G : GraphInput} (h : decode x = some G) : G.1 ≤ x.length := by
  unfold decode at h
  cases hs : unpairBits x with
  | none => simp [hs] at h
  | some xy =>
    rcases xy with ⟨header,payload⟩
    simp only [hs] at h
    split_ifs at h with hh
    · cases hg : MatrixGraph.ofBits header.length payload with
      | none => simp [hg] at h
      | some graph =>
        simp only [hg,Option.map_some,Option.some.injEq] at h
        subst G
        have hl := unpairBits_length hs
        simp only
        omega

end GraphInput
end HiddenCircuits.Complexity
