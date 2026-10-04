import HiddenCircuits.Approximation.SamplerRuntime.ArraySwap
import HiddenCircuits.Approximation.SamplerRuntime.IntervalCheck

/-! Actual endpoint-array reads followed by a physical half-open interval test. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.RowCheck
open Complexity Complexity.OracleBlock DH.Runtime

def check (ls hs : List BitString) (i : ℕ) (value : BitString) : Bool :=
  IntervalCheck.check (ls[i]?.getD []) (hs[i]?.getD []) value

def state (ls hs : BitString) (i : ℕ) (value out lo hi : BitString) : Store 11 := fun r =>
  if r.val=0 then ls else if r.val=1 then hs else if r.val=2 then List.replicate i true
  else if r.val=3 then value else if r.val=4 then out else if r.val=5 then lo else if r.val=6 then hi else []
def lowerMap : Fin 8 ↪ Fin 12 where
  toFun i := ![0,2,5,7,8,9,10,11] i
  inj' := by decide +kernel
def upperMap : Fin 8 ↪ Fin 12 where
  toFun i := ![1,2,6,7,8,9,10,11] i
  inj' := by decide +kernel
def compareMap : Fin 7 ↪ Fin 12 where
  toFun i := ![5,6,3,4,7,8,9] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 11 := seq (WordArray.readOn lowerMap)
  (seq (WordArray.readOn upperMap) (seq (IntervalCheck.on compareMap) (seq (clear 5) (clear 6))))
def bound (ls hs : List BitString) (i : ℕ) (value : BitString) : ℕ :=
  GraphReduction.Runtime.lookupBound (encodeBitList ls).length i+
    GraphReduction.Runtime.lookupBound (encodeBitList hs).length i+
    27*((ls[i]?.getD []).length+(hs[i]?.getD []).length)+26*value.length+60

theorem program_executes (g : BitString → ℕ) (ls hs : List BitString) (i : ℕ) (value : BitString) :
    ∃t,program.Executes g (state (encodeBitList ls) (encodeBitList hs) i value [] [] [])
      (state (encodeBitList ls) (encodeBitList hs) i value [check ls hs i value] [] []) t ∧
      t≤bound ls hs i value := by
  let l := ls[i]?.getD []
  let h := hs[i]?.getD []
  let L := encodeBitList ls
  let H := encodeBitList hs
  obtain ⟨a,ha,hba⟩ := WordArray.readOn_executes lowerMap g (state L H i value [] [] []) ls i
    (by funext r;fin_cases r <;> rfl)
  have ea : Function.update (state L H i value [] [] []) (lowerMap 2) l=state L H i value [] l [] := by
    funext r;fin_cases r <;> rfl
  change (WordArray.readOn lowerMap).Executes g _ (Function.update _ (lowerMap 2) l) a at ha
  rw [ea] at ha
  obtain ⟨b,hb,hbb⟩ := WordArray.readOn_executes upperMap g (state L H i value [] l []) hs i
    (by funext r;fin_cases r <;> rfl)
  have eb : Function.update (state L H i value [] l []) (upperMap 2) h=state L H i value [] l h := by
    funext r;fin_cases r <;> rfl
  change (WordArray.readOn upperMap).Executes g _ (Function.update _ (upperMap 2) h) b at hb
  rw [eb] at hb
  obtain ⟨c,hc,hbc⟩ := IntervalCheck.on_executes compareMap g (state L H i value [] l h) l h value
    (by funext r;fin_cases r <;> rfl)
  have ec : Function.update (state L H i value [] l h) (compareMap 3) [IntervalCheck.check l h value]=
      state L H i value [check ls hs i value] l h := by funext r;fin_cases r <;> rfl
  rw [ec] at hc
  have hd : (clear (5:Fin 12)).Executes g (state L H i value [check ls hs i value] l h)
      (state L H i value [check ls hs i value] [] h) (l.length+1) := by
    convert clear_executes g (5:Fin 12) _ using 1
    funext r;fin_cases r <;> rfl
  have he : (clear (6:Fin 12)).Executes g (state L H i value [check ls hs i value] [] h)
      (state L H i value [check ls hs i value] [] []) (h.length+1) := by
    convert clear_executes g (6:Fin 12) _ using 1
    funext r;fin_cases r <;> rfl
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb
    (seq_executes _ _ g hc (seq_executes _ _ g hd he))),?_⟩
  unfold bound
  dsimp [l,h] at *
  omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (WordArray.readOn_queryFree _)
  (seq_queryFree _ _ (WordArray.readOn_queryFree _) (seq_queryFree _ _ (IntervalCheck.on_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))
noncomputable def on {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (ls hs : List BitString) (i : ℕ) (value : BitString)
    (hs0 : s∘φ=state (encodeBitList ls) (encodeBitList hs) i value [] [] []) :
    ∃t,(on φ).Executes g s (Function.update s (φ 4) [check ls hs i value]) t ∧ t≤bound ls hs i value := by
  obtain ⟨t,ht,hb⟩ := program_executes g ls hs i value
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs0
  · have he : (Function.update s (φ 4) [check ls hs i value])∘φ=
        Function.update (s∘φ) 4 [check ls hs i value] := by
      funext r;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs0]
    funext r;fin_cases r <;> rfl
  · intro r hr;exact Function.update_of_ne (hr 4).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.RowCheck
