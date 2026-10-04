import HiddenCircuits.Approximation.Initialization.CandidateTestData
import HiddenCircuits.Approximation.Initialization.MaskData
import HiddenCircuits.Approximation.SamplerRuntime.PartnerEdge

/-! Actual retained-membership and graph-edge guard for a candidate.
All public inputs are preserved; the result is one Boolean and work is empty. -/
namespace HiddenCircuits.Approximation.Initialization.CandidateValidity
open Complexity Complexity.OracleBlock GraphVerifier GraphVerifier.Runtime

def state (N : ℕ) (payload mask : BitString) (u v : ℕ) (out member edge : BitString) : Store 11 := fun r =>
  if r.val=0 then List.replicate N true else if r.val=1 then payload else if r.val=2 then mask
  else if r.val=3 then List.replicate u true else if r.val=4 then List.replicate v true
  else if r.val=5 then out else if r.val=6 then member else if r.val=7 then edge else []
def maskPorts : Fin 5 ↪ Fin 12 where
  toFun r := if r.val=0 then 2 else if r.val=1 then 4 else if r.val=2 then 6 else ⟨r.val+5,by omega⟩
  inj' := by decide +kernel
def edgePorts : Fin 9 ↪ Fin 12 where
  toFun r := if r.val=0 then 0 else if r.val=1 then 3 else if r.val=2 then 4
    else if r.val=3 then 1 else if r.val=4 then 7 else ⟨r.val+3,by omega⟩
  inj' := by decide +kernel
noncomputable def finish : OracleBlock 11 := branchPop 7 (push 5 false) (push 5 false) (push 5 true)
noncomputable def accepted : OracleBlock 11 := seq (matrixLookupOn edgePorts) finish
noncomputable def program : OracleBlock 11 := seq (lookupOn maskPorts)
  (branchPop 6 (push 5 false) (push 5 false) accepted)

theorem pop_member (N u v : ℕ) (payload mask out edge : BitString) (b : Bool) :
    Function.update (state N payload mask u v out [b] edge) 6 [] = state N payload mask u v out [] edge := by
  funext r;fin_cases r <;> rfl
theorem pop_edge (N u v : ℕ) (payload mask out member : BitString) (b : Bool) :
    Function.update (state N payload mask u v out member [b]) 7 [] = state N payload mask u v out member [] := by
  funext r;fin_cases r <;> rfl

theorem finish_executes (g : BitString → ℕ) (N u v : ℕ) (payload mask : BitString) (b : Bool) :
    finish.Executes g (state N payload mask u v [] [] [b]) (state N payload mask u v [b] [] []) 3 := by
  have hp : (push (5 : Fin 12) b).Executes g (state N payload mask u v [] [] [])
      (state N payload mask u v [b] [] []) 1 := by
    convert push_executes g (5 : Fin 12) b _ using 1
    funext r;fin_cases r <;> rfl
  cases b
  · exact branchPop_false _ _ _ _ g rfl (by rw [pop_edge];exact hp)
  · exact branchPop_true _ _ _ _ g rfl (by rw [pop_edge];exact hp)

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N)
    (U : Finset (Fin N)) (u v : Fin N) :
    ∃ t, program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) u.val v.val [] [] [])
      (state N G.bits (MaskEnumerationSemantics.mask U) u.val v.val [CandidateTest.valid G U u v] [] []) t ∧
      t ≤ 14*N^2+31*N+35 := by
  let M := MaskEnumerationSemantics.mask U
  have hm : M[v.val]?.toList = [decide (v ∈ U)] := by simp [M,MaskEnumerationSemantics.mask,v.isLt]
  have h1 : (lookupOn maskPorts).Executes g (state N G.bits M u.val v.val [] [] [])
      (state N G.bits M u.val v.val [] [decide (v ∈ U)] [])
      (Lookup.cost M (List.replicate v.val true)) := by
    apply lookupOn_executes maskPorts g _ _ M (List.replicate v.val true)
    · funext r;fin_cases r <;> rfl
    · simp only [List.length_replicate,hm]
      funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r
      all_goals first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim | exact (hr 2 rfl).elim
  have h2 : ∃ t, (branchPop (6 : Fin 12) (push 5 false) (push 5 false) accepted).Executes g
      (state N G.bits M u.val v.val [] [decide (v ∈ U)] [])
      (state N G.bits M u.val v.val [CandidateTest.valid G U u v] [] []) t ∧
      t ≤ matrixLookupCost N u.val v.val G.bits+7 := by
    by_cases hv : v ∈ U
    · have he := matrixLookupOn_executes edgePorts g (state N G.bits M u.val v.val [] [] [])
        N u.val v.val G.bits (by funext r;fin_cases r <;> rfl)
      rw [SamplerRuntime.PartnerEdge.matrix_bit] at he
      have he' : (matrixLookupOn edgePorts).Executes g (state N G.bits M u.val v.val [] [] [])
          (state N G.bits M u.val v.val [] [] [G.edge u v]) (matrixLookupCost N u.val v.val G.bits) := by
        convert he using 1
        funext r;fin_cases r <;> simp [state,edgePorts]
      have hacc := seq_executes _ _ g he' (finish_executes g N u.val v.val G.bits M (G.edge u v))
      refine ⟨matrixLookupCost N u.val v.val G.bits+7,?_,le_rfl⟩
      simp only [CandidateTest.valid,decide_eq_true hv,Bool.true_and]
      apply branchPop_true (6 : Fin 12) _ _ _ g (rest := []) (by simp [state,hv])
      simpa only [pop_member] using hacc
    · refine ⟨3,?_,by omega⟩
      have ho : CandidateTest.valid G U u v = false := by simp [CandidateTest.valid,hv]
      rw [ho]
      apply branchPop_false (6 : Fin 12) _ _ _ g (rest := []) (by simp [state,hv])
      rw [pop_member]
      convert push_executes g (5 : Fin 12) false _ using 1
      funext r;fin_cases r <;> rfl
  obtain ⟨a,ha,hab⟩ := h2
  refine ⟨_,seq_executes _ _ g h1 ha,?_⟩
  have hl := Lookup.cost_bound M (List.replicate v.val true)
  simp only [List.length_replicate] at hl
  have he := matrixLookupCost_bound N u.val v.val G.bits
  have hu := u.isLt
  have hv := v.isLt
  have hh : N*u.val ≤ N*N := Nat.mul_le_mul_left N hu.le
  nlinarith

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (lookupOn_queryFree _)
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _)
    (seq_queryFree _ _ (matrixLookupOn_queryFree _)
      (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _))))

noncomputable def on {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) : OracleBlock k := rename program φ
theorem on_executes {k N : ℕ} (φ : Fin 12 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (G : MatrixGraph N) (U : Finset (Fin N)) (u v : Fin N)
    (hs : s ∘ φ = state N G.bits (MaskEnumerationSemantics.mask U) u.val v.val [] [] []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 5) [CandidateTest.valid G U u v]) t ∧
      t ≤ 14*N^2+31*N+35 := by
  obtain ⟨t,ht,hb⟩ := program_executes g G U u v
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · funext r
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    have hh := congrFun hs r
    simp only [Function.comp_apply] at hh
    rw [hh]
    fin_cases r <;> rfl
  · intro r hr
    exact Function.update_of_ne (hr 5).symm _ _
theorem on_queryFree {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.Initialization.CandidateValidity
