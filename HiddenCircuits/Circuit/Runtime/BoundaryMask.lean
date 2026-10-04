import HiddenCircuits.Complexity.WordEncoding
import HiddenCircuits.Circuit.BitAssignments
import HiddenCircuits.LogicalConcat

namespace HiddenCircuits.Circuit.Runtime.BoundaryMask
open HiddenCircuits.Complexity

theorem stateBits_join {a b u v : ℕ} (S : State a u) (T : State b v) :
    stateBits (State.join S T)=stateBits S++stateBits T := by
  unfold stateBits
  rw [List.ofFn_add]
  simp only [State.join_mem_right]
  congr 1
  apply congrArg List.ofFn
  funext i
  change decide (Fin.castAdd b i∈(State.join S T).val)=decide (i∈S.val)
  simp only [State.join_mem_left]

theorem stateBits_castParticles {n q r : ℕ} (h : q=r) (S : State n q) :
    stateBits (State.castParticles h S)=stateBits S := rfl

theorem stateBits_castTracks {n m q : ℕ} (h : n=m) (S : State n q) :
    stateBits (State.castTracks h S)=stateBits S := by subst m;rfl

def mask (n : ℕ) : BitString := (List.replicate n [true,false,true,false]).flatten

theorem local_zero : stateBits (localRawCode 0)=[true,false,true,false] := by decide

theorem zero_mask (n : ℕ) : stateBits (rawCode n (zeroBits n))=mask n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change stateBits (State.castParticles (by omega) (State.join (localRawCode 0) (rawCode n (zeroBits n))))=mask (n+1)
    rw [stateBits_castParticles,stateBits_join,local_zero,ih]
    simp [mask,List.replicate_succ]

@[simp] theorem mask_length (n : ℕ) : (mask n).length=4*n := by simp [mask];omega
end HiddenCircuits.Circuit.Runtime.BoundaryMask
