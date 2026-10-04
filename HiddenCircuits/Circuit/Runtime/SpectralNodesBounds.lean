import HiddenCircuits.Circuit.Runtime.SpectralNodesOuterLoop
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsLoop

namespace HiddenCircuits.Circuit.Runtime.SpectralNodes
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic

theorem stages_bounded (n : ℕ) : StageBound 1 n (4*n+2) := by
  intro a ha b hb
  let i : SpectralIndex n := ⟨⟨a,by omega⟩,⟨b,by change b<n-a+1;omega⟩⟩
  have hnode := spectralIntegerNode_bound i
  change (spectralIntegerNode i).natAbs≤2^(4*n) at hnode
  have hlt : (spectralIntegerNode i).natAbs<2^(4*n+1) := by
    rw [pow_succ]
    have hp : 0<(2:ℕ)^(4*n) := by positivity
    omega
  have hs := Nat.size_le.mpr hlt
  have he : spectralIntegerNode i=((1*4^a*9^b:ℕ):ℤ) := by
    simp [spectralIntegerNode,spectralNode,i]
  rw [he] at hs
  simp only [signedBits,List.length_cons,encodeNat_length]
  omega

theorem triangle_stream_length (n : ℕ) :
    (encodeBitList ((triangle 1 n).map signedBits)).length≤n*n*(2*(4*n+2)+2) := by
  have hb : ∀y∈triangle (1:ℤ) n,(signedBits y).length≤4*n+2 := by
    intro y hy
    rw [triangle_eq_range] at hy
    obtain ⟨a,ha,hy⟩ := List.mem_flatMap.mp hy
    rw [row_eq_range] at hy
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
    have h := stages_bounded n a (by have := List.mem_range.mp ha;omega) b (by have := List.mem_range.mp hb;omega)
    simpa using h
  have hl := triangle_length_le (1:ℤ) n
  have he := encodedWords_length_le ((triangle (1:ℤ) n).map signedBits) (4*n+2) (by
    intro w hw
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
    exact hb y hy)
  simp only [List.length_map] at he
  exact he.trans (Nat.mul_le_mul_right _ hl)

end HiddenCircuits.Circuit.Runtime.SpectralNodes
