import HiddenCircuits.Approximation.SamplerRuntime.Output
import HiddenCircuits.Approximation.Initialization.RawExtraction
import HiddenCircuits.Approximation.Initialization.MaskEnumerationSemantics
import HiddenCircuits.Approximation.SelfReduction.Runtime.FirstTrue

/-! Exact public bank and residual termination code
for the graph-only 52-stack matching initializer. -/
namespace HiddenCircuits.Approximation.Initialization.OuterLoop
open Complexity Complexity.OracleBlock SamplerRuntime
abbrev unary (n : ℕ) : BitString := List.replicate n true

def state (N : ℕ) (payload mask source : BitString) (B : ℕ) (data : BitString)
    (L fuel : ℕ) (ok : BitString) : Store 51 := fun r =>
  if r.val=0 then unary N else if r.val=1 then payload else if r.val=2 then mask
  else if r.val=3 then source else if r.val=4 then unary B else if r.val=5 then data
  else if r.val=6 then unary L else if r.val=7 then ok
  else if r.val=51 then unary fuel else []

noncomputable def result {N : ℕ} (U : Finset (Fin N)) (π : Equiv.Perm (Fin N)) :
    Option (Equiv.Perm (Fin N)) := if U=∅ then some π else none

def loopBound (T fuel : ℕ) : ℕ := fuel*(T+2*fuel+10)+1

@[simp] lemma result_empty {N : ℕ} (π : Equiv.Perm (Fin N)) : result ∅ π=some π := by simp [result]
lemma result_nonempty {N : ℕ} (U : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (hU : U.Nonempty) :
    result U π=none := by simp [result,Finset.nonempty_iff_ne_empty.mp hU]

lemma witness_length_le {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (Output.witness π).length≤2*N^2+2*N := by
  unfold Output.witness Switch.rowWords GraphReduction.MonotoneEndpointEncoding.rows
  have h : ∀ (xs : List BitString), (∀ x∈xs,x.length≤N) →
      (encodeBitList xs).length≤xs.length*(2*N+2) := by
    intro xs
    induction xs with
    | nil => simp [encodeBitList]
    | cons x xs ih =>
      intro hx
      have hxl := hx x (by simp)
      have htail := ih (fun y hy => hx y (by simp [hy]))
      simp only [encodeBitList,List.length_cons,pairBits_length]
      nlinarith
  simpa [pow_two,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
    h (List.ofFn (fun i : Fin N => List.replicate (π i).val true))
      (by intro x hx;obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx;simp)

end HiddenCircuits.Approximation.Initialization.OuterLoop
