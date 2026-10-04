import HiddenCircuits.Approximation.SamplerRuntime.GraphValidation

/-! Total literal graph parser: preserved raw bytes0, exact validity1,
adjacency payload2, unary header3, and all remaining work empty. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphParser
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime Polynomial
set_option maxHeartbeats 800000

def output (raw : BitString) : Store 38 := fun q =>
  if q.val=0 then raw else if q.val=1 then [(GraphInput.decode raw).isSome]
  else if q.val=2 then (parse raw).right else if q.val=3 then (parse raw).left else []
def parsed (raw : BitString) : Store 38 := Function.update (output raw) 5 [(parse raw).ok]
def parseMap : Fin 4 ↪ Fin 39 where
  toFun q := ![2,3,4,5] q
  inj' := by decide +kernel
noncomputable def program : OracleBlock 38 := seq validate
  (seq (copyOn 0 2 4 (by decide) (by decide) (by decide)) (seq (unpairOn parseMap) (clear 5)))
noncomputable def time : Polynomial ℕ := validationTime+20*(X+1)

theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃c,program.Executes g (Function.update (fun _ : Fin 39 => ([]:BitString)) 0 raw) (output raw) c ∧
      c≤time.eval raw.length := by
  obtain ⟨a,ha,hab⟩ := validate_executes g raw
  let mid := validationStore raw [(GraphInput.decode raw).isSome] raw []
  have hb : (copyOn (0:Fin 39) 2 4 (by decide) (by decide) (by decide)).Executes g
      (validationStore raw [(GraphInput.decode raw).isSome] [] []) mid (5*raw.length+2) := by
    convert copyOn_executes g (0:Fin 39) 2 4 (by decide) (by decide) (by decide)
      (validationStore raw [(GraphInput.decode raw).isSome] [] []) rfl using 1
    funext q;fin_cases q <;> simp [mid,validationStore]
  have hc : (unpairOn parseMap).Executes g mid (parsed raw) (parseCost raw+2*(parse raw).left.length+1) := by
    apply unpairOn_executes parseMap g mid (parsed raw) raw
    · funext q;fin_cases q <;> rfl
    · funext q;fin_cases q <;> rfl
    · intro q hq
      have h2:q≠2:=by intro h;subst q;exact hq 0 rfl
      have h3:q≠3:=by intro h;subst q;exact hq 1 rfl
      have h5:q≠5:=by intro h;subst q;exact hq 3 rfl
      simp only [parsed,Function.update_of_ne h5,mid,validationStore,output,
        show q.val≠2 from fun h=>h2 (Fin.ext h),show q.val≠3 from fun h=>h3 (Fin.ext h),if_false]
  have hd : (clear (5:Fin 39)).Executes g (parsed raw) (output raw) 2 := by
    convert clear_executes g (5:Fin 39) (parsed raw) using 1
    funext q;fin_cases q <;> simp [parsed,output]
  have hi : validationStore raw [] [] []=Function.update (fun _ : Fin 39 => ([]:BitString)) 0 raw := by
    funext q;fin_cases q <;> rfl
  rw [hi] at ha
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),?_⟩
  have hp := unpair_cost_bound raw
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  omega
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ validate_queryFree
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (unpairOn_queryFree _) (clear_queryFree _)))
lemma output_valid (raw : BitString) : output raw 1=[(GraphInput.decode raw).isSome] := rfl
lemma output_fields {raw : BitString} {G : GraphInput} (h : GraphInput.decode raw=some G) :
    output raw 3=List.replicate G.1 true ∧ output raw 2=G.2.bits := fields_of_decode h
lemma output_clean (raw : BitString) (i : Fin 39) (h : 4 ≤ i.val) : output raw i=[] := by
  simp [output,show i.val≠0 by omega,show i.val≠1 by omega,show i.val≠2 by omega,show i.val≠3 by omega]
end HiddenCircuits.Approximation.SamplerRuntime.GraphParser
