import HiddenCircuits.Approximation.SamplerRuntime.ReadLess

/-! A fixed seven-stack comparison of half-open unary endpoint intervals. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.IntervalCheck
open Complexity Complexity.OracleBlock

def check (lo hi value : BitString) : Bool := decide (lo.length≤value.length ∧ value.length<hi.length)
def state (lo hi value out : BitString) : Store 6 := fun r =>
  if r.val=0 then lo else if r.val=1 then hi else if r.val=2 then value else if r.val=3 then out else []
def lowerMap : Fin 6 ↪ Fin 7 where
  toFun i := ![2,0,3,4,5,6] i
  inj' := by decide +kernel
def upperMap : Fin 6 ↪ Fin 7 where
  toFun i := ![2,1,3,4,5,6] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 6 := seq (LengthLess.readLessOn lowerMap)
  (branchPop 3 (LengthLess.readLessOn upperMap) (LengthLess.readLessOn upperMap) (push 3 false))

lemma flag_pop (lo hi value : BitString) (b : Bool) :
    Function.update (state lo hi value [b]) 3 []=state lo hi value [] := by
  funext r;fin_cases r <;> rfl

theorem program_executes (g : BitString → ℕ) (lo hi value : BitString) :
    ∃t,program.Executes g (state lo hi value []) (state lo hi value [check lo hi value]) t ∧
      t≤26*(lo.length+hi.length+value.length)+50 := by
  obtain ⟨c,hc,hcb⟩ := LengthLess.readLessOn_executes lowerMap g (state lo hi value []) value lo
    (by funext r;fin_cases r <;> rfl)
  have he : Function.update (state lo hi value []) (lowerMap 2) [decide (value.length<lo.length)]=
      state lo hi value [decide (value.length<lo.length)] := by funext r;fin_cases r <;> rfl
  rw [he] at hc
  by_cases hl : value.length<lo.length
  · simp only [hl,decide_true] at hc
    have hp : (push (3:Fin 7) false).Executes g (state lo hi value []) (state lo hi value [false]) 1 := by
      convert push_executes g (3:Fin 7) false (state lo hi value []) using 1
      funext r;fin_cases r <;> rfl
    have hb := branchPop_true (3:Fin 7) (LengthLess.readLessOn upperMap) (LengthLess.readLessOn upperMap)
      (push 3 false) g (s:=state lo hi value [true]) rfl (by rw [flag_pop];exact hp)
    refine ⟨c+(1+2)+2,?_,by omega⟩
    have hcheck : check lo hi value=false := by simp [check,show ¬lo.length≤value.length by omega]
    rw [hcheck]
    exact seq_executes _ _ g hc hb
  · simp only [hl,decide_false] at hc
    obtain ⟨d,hd,hdb⟩ := LengthLess.readLessOn_executes upperMap g (state lo hi value []) value hi
      (by funext r;fin_cases r <;> rfl)
    have he' : Function.update (state lo hi value []) (upperMap 2) [decide (value.length<hi.length)]=
        state lo hi value [check lo hi value] := by
      funext r;fin_cases r <;> simp [state,check,show lo.length≤value.length by omega,upperMap]
    rw [he'] at hd
    have hb := branchPop_false (3:Fin 7) (LengthLess.readLessOn upperMap) (LengthLess.readLessOn upperMap)
      (push 3 false) g (s:=state lo hi value [false]) rfl (by rw [flag_pop];exact hd)
    exact ⟨_,seq_executes _ _ g hc hb,by omega⟩

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (LengthLess.readLessOn_queryFree _)
  (branchPop_queryFree _ _ _ _ (LengthLess.readLessOn_queryFree _) (LengthLess.readLessOn_queryFree _) (push_queryFree _ _))

noncomputable def on {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (lo hi value : BitString) (hs : s∘φ=state lo hi value []) :
    ∃t,(on φ).Executes g s (Function.update s (φ 3) [check lo hi value]) t ∧
      t≤26*(lo.length+hi.length+value.length)+50 := by
  obtain ⟨t,ht,hb⟩ := program_executes g lo hi value
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 3) [check lo hi value])∘φ=
        Function.update (s∘φ) 3 [check lo hi value] := by
      funext r;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext r;fin_cases r <;> rfl
  · intro r hr;exact Function.update_of_ne (hr 3).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 7 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.IntervalCheck
