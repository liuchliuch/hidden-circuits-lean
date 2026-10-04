import HiddenCircuits.Circuit.Runtime.GateEncoding
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! A fixed finite four-bit dispatch tree for canonical constraint-gate tags. -/
namespace HiddenCircuits.Circuit.Runtime.SampleGateDispatch
open HiddenCircuits.Complexity OracleBlock

noncomputable def readBits {k : ℕ} (stack : Fin (k+1)) : ℕ → (BitString → OracleBlock k) → OracleBlock k
  | 0,f => f []
  | d+1,f => branchPop stack skip (readBits stack d (fun bs => f (false::bs)))
      (readBits stack d (fun bs => f (true::bs)))

theorem readBits_executes {k : ℕ} (stack : Fin (k+1)) (g : BitString → ℕ)
    (bits rest : BitString) (f : BitString → OracleBlock k) (s t : Store k) (cost : ℕ)
    (hs : s stack=bits++rest) (hf : (f bits).Executes g (Function.update s stack rest) t cost) :
    (readBits stack bits.length f).Executes g s t (cost+2*bits.length) := by
  induction bits generalizing f s with
  | nil =>
    have he : Function.update s stack rest=s := by
      have hr : rest=s stack := by simpa using hs.symm
      simp only [hr,Function.update_eq_self]
    simpa only [readBits,List.length_nil,Nat.mul_zero,Nat.add_zero,he] using hf
  | cons b bits ih =>
    have hp : s stack=b::(bits++rest) := hs
    have ht : (readBits stack bits.length (fun bs => f (b::bs))).Executes g
        (Function.update s stack (bits++rest)) t (cost+2*bits.length) := by
      apply ih (fun bs => f (b::bs)) (Function.update s stack (bits++rest)) (by simp)
      simpa only [Function.update_idem] using hf
    have h : (readBits stack (b::bits).length f).Executes g s t (cost+2*bits.length+2) := by
      cases b
      · exact branchPop_false _ _ _ _ g hp ht
      · exact branchPop_true _ _ _ _ g hp ht
    convert h using 1 <;> simp [List.length_cons] <;> omega

lemma readBits_queryFree {k : ℕ} (stack : Fin (k+1)) (d : ℕ) (f : BitString → OracleBlock k)
    (hf : ∀ bs, (f bs).QueryFree) : (readBits stack d f).QueryFree := by
  induction d generalizing f with
  | zero => exact hf []
  | succ d ih => exact branchPop_queryFree _ _ _ _ skip_queryFree (ih _ (fun _ => hf _)) (ih _ (fun _ => hf _))

noncomputable def block {k : ℕ} (stack : Fin (k+1)) (body : GateTag → OracleBlock k) : OracleBlock k :=
  readBits stack 4 (fun bs => match decodeTag bs with | none => skip | some a => body a)

theorem block_executes {k : ℕ} (stack : Fin (k+1)) (body : GateTag → OracleBlock k)
    (g : BitString → ℕ) (a : GateTag) (s t : Store k) (cost : ℕ)
    (hs : s stack=a.bits) (hb : (body a).Executes g (Function.update s stack []) t cost) :
    (block stack body).Executes g s t (cost+8) := by
  have h := readBits_executes stack g a.bits []
    (fun bs => match decodeTag bs with | none => skip | some a => body a) s t cost
    (by simpa using hs) (by simpa only [decodeTag_bits] using hb)
  simpa only [GateTag.bits_length] using h

lemma block_queryFree {k : ℕ} (stack : Fin (k+1)) (body : GateTag → OracleBlock k)
    (hb : ∀ a, (body a).QueryFree) : (block stack body).QueryFree := by
  apply readBits_queryFree
  intro bs
  cases decodeTag bs with
  | none => exact skip_queryFree
  | some a => exact hb a

end HiddenCircuits.Circuit.Runtime.SampleGateDispatch
