import HiddenCircuits.GraphReduction.Runtime.CliqueDescriptor
import HiddenCircuits.GraphReduction.Runtime.DirectedPredicate

namespace HiddenCircuits.GraphReduction.Runtime.PrivateCut
open Complexity OracleBlock
set_option maxHeartbeats 800000

def cut (lower : Bool) (x y : VertexRecord) : Bool :=
  if lower then cutBit y.cut.rightRise y.cut.rightDrop y.cut.index x.track y.track
  else cutBit y.cut.leftRise y.cut.leftDrop y.cut.index x.track y.track

def finalGate (mode : Bool) : List Bool → Bool
  | [_,_,_,_,_,_,first,second] => if mode then second else first
  | _ => false
noncomputable def finish (mode : Bool) : OracleBlock 40 := gate8On dirFinalEmbedding (finalGate mode)
noncomputable def boolean (mode : Bool) : OracleBlock 40 := seq dirBoolean (seq (clear 18) (finish mode))
noncomputable def program (mode : Bool) : OracleBlock 40 :=
  seq dirPrepare (seq dirCompare (seq (boolean mode) (clearList dirWork)))

lemma finish_executes (g : BitString → ℕ) (mode : Bool) (x y : VertexRecord) :
    (finish mode).Executes g (dirState x y 11) (dirState x y 11 [cut mode x y]) 92 := by
  let bits : Fin 8 → Bool := ![x.side,y.side,x.probe,y.probe,dirBits x y 0,dirBits x y 1,dirBits x y 9,dirBits x y 10]
  have hc := gate8On_executes dirFinalEmbedding g (finalGate mode) bits (dirState x y 11)
    (by funext i;fin_cases i <;> rfl)
  have he : finalGate mode (gate8Args bits)=cut mode x y := by
    simp [bits,gate8Args,finalGate,dirBits,cut]
  rw [he] at hc
  convert hc using 1
  funext i;fin_cases i <;> rfl

lemma boolean_executes (g : BitString → ℕ) (mode : Bool) (x y : VertexRecord) :
    (boolean mode).Executes g (dirState x y 6) (dirState x y 11 [cut mode x y]) 660 := by
  have hc : (clear (18:Fin 41)).Executes g (dirState x y 11 [directedRecordAdj x y]) (dirState x y 11) 2 := by
    convert clear_executes g (18:Fin 41) (dirState x y 11 [directedRecordAdj x y]) using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ g (dirBoolean_executes g x y) (seq_executes _ _ g hc (finish_executes g mode x y))

theorem program_executes (g : BitString → ℕ) (mode : Bool) (x y : VertexRecord) :
    ∃c,(program mode).Executes g (dirStore x y [] [] (fun _=>[]) [])
      (dirStore x y [] [] (fun _=>[]) [cut mode x y]) c ∧ c≤200*dirSize x y+1000 := by
  have hp := dirPrepare_executes g x y
  obtain ⟨c,hc,hcb⟩ := dirCompare_executes g x y
  have hb := boolean_executes g mode x y
  obtain ⟨t,ht,htb⟩ := clearList_executes g dirWork (dirState x y 11 [cut mode x y])
    (dirSize x y) (dirState_length x y 11 [cut mode x y] (by simp))
  have he : eraseStore dirWork (dirState x y 11 [cut mode x y])=
      dirStore x y [] [] (fun _=>[]) [cut mode x y] := by
    funext i;fin_cases i <;> simp [eraseStore,dirWork,dirState,dirStore]
  rw [he] at ht
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hb ht)),?_⟩
  have hh := dir_coordinates_bound x y
  simp only [dirWork,List.length_cons,List.length_nil] at htb
  omega

lemma program_queryFree (mode : Bool) : (program mode).QueryFree := seq_queryFree _ _ dirPrepare_queryFree
  (seq_queryFree _ _ dirCompare_queryFree (seq_queryFree _ _
    (seq_queryFree _ _ dirBoolean_queryFree (seq_queryFree _ _ (clear_queryFree _) (gate8On_queryFree _ _))) (clearList_queryFree _)))
noncomputable def on {k : ℕ} (φ : Fin 41 ↪ Fin (k+1)) (mode : Bool) : OracleBlock k := rename (program mode) φ

theorem on_executes {k : ℕ} (φ : Fin 41 ↪ Fin (k+1)) (g : BitString → ℕ) (mode : Bool)
    (x y : VertexRecord) (s : Store k) (hs : s∘φ=dirStore x y [] [] (fun _=>[]) []) :
    ∃c,(on φ mode).Executes g s (Function.update s (φ 18) [cut mode x y]) c ∧ c≤200*dirSize x y+1000 := by
  obtain ⟨c,hc,hb⟩ := program_executes g mode x y
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (program mode) φ g hc hs
  · have he : (Function.update s (φ 18) [cut mode x y])∘φ=
        Function.update (s∘φ) 18 [cut mode x y] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 18).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 41 ↪ Fin (k+1)) (mode : Bool) : (on φ mode).QueryFree := rename_queryFree _ _ (program_queryFree mode)
end HiddenCircuits.GraphReduction.Runtime.PrivateCut
