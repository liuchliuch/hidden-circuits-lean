import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! Consume a signed integer and leave its literal sign bit. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.SignFlag
open OracleBlock
noncomputable def branch (b : Bool) : OracleBlock 1 := seq (clear 0) (push 1 b)
noncomputable def program : OracleBlock 1 := branchPop 0 (push 1 false) (branch false) (branch true)

theorem program_executes (g : BitString → ℕ) (sign : Bool) (mag : BitString) :
    program.Executes g (pairStore (sign::mag) []) (pairStore [] [sign]) (mag.length+6) := by
  have hc : (clear (0:Fin 2)).Executes g (pairStore mag []) (pairStore [] []) (mag.length+1) := by
    convert clear_executes g (0:Fin 2) (pairStore mag []) using 1
    funext i;fin_cases i <;> rfl
  have hp : (push (1:Fin 2) sign).Executes g (pairStore [] []) (pairStore [] [sign]) 1 := by
    convert push_executes g (1:Fin 2) sign (pairStore [] []) using 1
    funext i;fin_cases i <;> rfl
  have hb:=seq_executes _ _ g hc hp
  have he : Function.update (pairStore (sign::mag) []) 0 mag=pairStore mag [] := by funext i;fin_cases i <;> rfl
  cases sign
  · convert branchPop_false (0:Fin 2) _ _ _ g rfl (by rw [he];exact hb) using 1 <;> omega
  · convert branchPop_true (0:Fin 2) _ _ _ g rfl (by rw [he];exact hb) using 1 <;> omega
lemma program_queryFree : program.QueryFree := branchPop_queryFree _ _ _ _ (push_queryFree _ _)
  (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))
noncomputable def on {k : ℕ} (source target : Fin (k+1)) (hne:source≠target) : OracleBlock k :=
  rename program (pairEmbedding source target hne)

theorem on_executes {k : ℕ} (source target : Fin (k+1)) (hne:source≠target) (g : BitString → ℕ)
    (s : Store k) (z : ℤ) (hs:s source=signedBits z) (ht:s target=[]) :
    (on source target hne).Executes g s (Function.update (Function.update s source []) target [negative z])
      ((signedBits z).length+5) := by
  have hh:=rename_executes program (pairEmbedding source target hne) g s
    (by rw [restrict_pair,hs,ht];exact program_executes g (negative z) (Computability.encodeNat z.natAbs))
  simpa only [install_pair,signedBits,List.length_cons,Nat.add_assoc] using hh
lemma on_queryFree {k : ℕ} (source target : Fin (k+1)) (hne:source≠target) : (on source target hne).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Complexity.BinaryArithmetic.SignFlag
