import HiddenCircuits.GraphReduction.Runtime.UnitCorrectionGates
import HiddenCircuits.GraphReduction.Runtime.LocalCleanup

namespace HiddenCircuits.GraphReduction.Runtime.UnitCorrection
open Complexity Complexity.OracleBlock
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

def output (second : Bool) (width : ℕ) (x y : VertexRecord) : BitString :=
  [decide (unitCorrectionValue second width x y=1),decide (unitCorrectionValue second width x y=-1)]
def cleanPorts : List (Fin 49) := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
noncomputable def finish : OracleBlock 48 :=
  seq (copyOn 35 19 44 (by decide) (by decide) (by decide))
    (seq (copyOn 33 19 44 (by decide) (by decide) (by decide)) (clearList cleanPorts))
noncomputable def program (second : Bool) : OracleBlock 48 := seq prepare (seq compareAll (seq (gateAll second) finish))

theorem finish_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,finish.Executes g (state second width x y 2 14)
      (state second width x y 0 0 (output second width x y)) t ∧t≤16*(size width x y+3)+19 := by
  let s1:=state second width x y 2 14 [negative second width x y]
  let s2:=state second width x y 2 14 [positive second width x y,negative second width x y]
  have h1 : (copyOn (35:Fin 49) 19 44 (by decide) (by decide) (by decide)).Executes g
      (state second width x y 2 14) s1 7 := by
    convert copyOn_executes g (35:Fin 49) 19 44 (by decide) (by decide) (by decide)
      (state second width x y 2 14) rfl using 1
    funext i;fin_cases i <;> rfl
  have h2 : (copyOn (33:Fin 49) 19 44 (by decide) (by decide) (by decide)).Executes g s1 s2 7 := by
    convert copyOn_executes g (33:Fin 49) 19 44 (by decide) (by decide) (by decide) s1 rfl using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨t,ht,hb⟩ := clearList_executes_local g cleanPorts s2 (size width x y) (by
    intro j hj
    simp only [cleanPorts,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [s2,state,size] <;> omega)
  have he : eraseStore cleanPorts s2=state second width x y 0 0 (output second width x y) := by
    unfold output
    rw [←positive_eq,←negative_eq]
    funext i;fin_cases i <;> rfl
  rw [he] at ht
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 ht),?_⟩
  simp only [cleanPorts,List.length_cons,List.length_nil] at hb
  omega

theorem program_executes (g : BitString → ℕ) (second : Bool) (width : ℕ) (x y : VertexRecord) :
    ∃t,(program second).Executes g (state second width x y 0 0)
      (state second width x y 0 0 (output second width x y)) t ∧t≤1000*size width x y+2000 := by
  have h1:=prepare_executes g second width x y
  obtain ⟨b,h2,hb⟩:=compareAll_executes g second width x y
  have h3:=gateAll_executes g second width x y
  obtain ⟨d,h4,hd⟩:=finish_executes g second width x y
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  unfold size at *;omega
lemma program_queryFree (second : Bool) : (program second).QueryFree :=
  seq_queryFree _ _ prepare_queryFree (seq_queryFree _ _ compareAll_queryFree (seq_queryFree _ _ (gateAll_queryFree second)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (clearList_queryFree _)))))

noncomputable def on {k : ℕ} (φ : Fin 49 ↪ Fin (k+1)) (second : Bool) : OracleBlock k := rename (program second) φ
theorem on_executes {k : ℕ} (φ : Fin 49 ↪ Fin (k+1)) (g : BitString → ℕ) (second : Bool)
    (width : ℕ) (x y : VertexRecord) (s : Store k) (hs:s∘φ=state second width x y 0 0) :
    ∃t,(on φ second).Executes g s (Function.update s (φ 19) (output second width x y)) t ∧t≤1000*size width x y+2000 := by
  obtain ⟨t,ht,hb⟩:=program_executes g second width x y
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · have he : (Function.update s (φ 19) (output second width x y))∘φ=
        Function.update (s∘φ) 19 (output second width x y) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 19).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 49 ↪ Fin (k+1)) (second : Bool) : (on φ second).QueryFree :=
  rename_queryFree _ _ (program_queryFree second)
end HiddenCircuits.GraphReduction.Runtime.UnitCorrection
