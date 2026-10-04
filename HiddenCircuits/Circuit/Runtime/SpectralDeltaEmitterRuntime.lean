import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterFinish
import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterBounds

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
open Complexity OracleBlock Polynomial

noncomputable def program : OracleBlock 15 := seq setup (seq loop finish)
noncomputable def time : Polynomial ℕ := 5000*(X+1)^3

theorem program_executes (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    ∃ cost, program.Executes g (store (circuitBits n w) r s 0 [] [] [] [] [] [] [] [])
      (store (circuitBits n w) r s 0 [] [] [] [] [] [] [] (query w r s).encode) cost ∧
      cost ≤ time.eval ((circuitBits n w).length+r+s) := by
  have hs:=setup_executes g w r s
  obtain ⟨c,hc,hcb⟩:=loop_execution g w (circuitBits n w) r s [] [] [] []
  simp only [List.append_nil] at hc
  have hf:=finish_executes g w r s
  refine ⟨_,seq_executes _ _ g hs (seq_executes _ _ g (whilePop_executes _ _ _ g hc) hf),?_⟩
  clear hs hc hf
  let N:=(circuitBits n w).length+r+s+1
  obtain ⟨hn,hw⟩:=circuit_size_bounds w
  have hN : 1 ≤ N := by dsimp [N];omega
  have hnN : n ≤ N := by dsimp [N];omega
  have hwN : w.length ≤ N := by dsimp [N];omega
  have hrs : r+s ≤ N := by dsimp [N];omega
  have hL : (circuitBits n w).length ≤ N := by dsimp [N];omega
  have hN₂ : N ≤ N^2 := by nlinarith
  have hN₃ : N^2 ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN₂]
  have hout:=output_length w r s
  have hm₁ : 2*(r+s)+1 ≤ 3*N := by omega
  have hm₂ : 2*n+20 ≤ 22*N := by omega
  have hmul:=Nat.mul_le_mul hwN (Nat.mul_le_mul hm₁ hm₂)
  have ho : (output w r s).length ≤ 66*N^3 := by nlinarith
  have hgate : gateTime n r s ≤ 271*N^2 := by
    have hb : 14*n+70 ≤ 84*N := by omega
    have hm:=Nat.mul_le_mul hm₁ hb
    unfold gateTime
    nlinarith
  have hloop:=Nat.mul_le_mul hwN (show gateTime n r s+6*n+99 ≤ 376*N^2 by nlinarith)
  simp only [time,eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change _ ≤ 5000*N^3
  nlinarith

lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (reverseOn_queryFree _ _ _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (PairSerialization.on_queryFree _)
    (seq_queryFree _ _ hz (seq_queryFree _ _ hz (clear_queryFree _))))) where
  hz : zeroPair.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (PairSerialization.on_queryFree _))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ setup_queryFree (seq_queryFree _ _ loop_queryFree finish_queryFree)
end HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
