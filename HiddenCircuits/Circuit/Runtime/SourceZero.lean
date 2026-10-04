import HiddenCircuits.Circuit.Runtime.GateEncoding
import HiddenCircuits.Complexity.OracleCleanup

/-! The degenerate source graph has one independent set,
and the zero-wire branch writes its canonical answer by actual instructions. -/
namespace HiddenCircuits.Circuit.Runtime.SourceZero
open HiddenCircuits.Complexity OracleBlock

theorem no_gate (a : ConstraintGate 0) : False := by
  have h:=gatePosition_bound a
  cases a with
  | one p g => cases g <;> simp [gateTag,GateTag.width] at h
  | forbid p => simp [gateTag,GateTag.width] at h
  | controlledSign p => simp [gateTag,GateTag.width] at h

theorem gates_nil (w : List (ConstraintGate 0)) : w=[] := by
  cases w with
  | nil => rfl
  | cons a w => exact (no_gate a).elim

theorem independentCount_zero (G : MatrixGraph 0) : G.independentCount=1 := by
  classical
  rw [MatrixGraph.independentCount_eq_certificates]
  have hvalid (w : Fin 0 → Bool) : G.ValidIndependent w := by intro i;exact Fin.elim0 i
  simp [MatrixGraph.IndependentCertificate,hvalid]

noncomputable def on {k : ℕ} (out : Fin (k+1)) : OracleBlock k := seq (clear out) (push out true)

theorem on_executes {k : ℕ} (out : Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (hs : (s out).length=1) :
    (on out).Executes g s (Function.update s out (Computability.encodeNat 1)) 5 := by
  have hc := clear_executes g out s
  have hp := push_executes g out true (Function.update s out [])
  have h := seq_executes _ _ g hc hp
  simpa only [Function.update_self,Function.update_idem,hs,Computability.encodeNat] using h

lemma on_queryFree {k : ℕ} (out : Fin (k+1)) : (on out).QueryFree :=
  seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)

theorem wire_positive {n : ℕ} (w : List (ConstraintGate n)) (h : w≠[]) : 0<n := by
  by_contra hn
  have hn' : n=0 := by omega
  subst n
  exact h (gates_nil w)
end HiddenCircuits.Circuit.Runtime.SourceZero
