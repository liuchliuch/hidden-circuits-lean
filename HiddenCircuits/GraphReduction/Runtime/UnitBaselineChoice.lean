import HiddenCircuits.GraphReduction.Runtime.UnitBaselineCode
import HiddenCircuits.GraphReduction.Runtime.BitProgramChoice
import HiddenCircuits.GraphReduction.Runtime.SeedFlags

/-! A finite Boolean branch tree selects the concrete affine code.
Its input flags are ordinary descriptor fields plus the computed track equality.
The selected leaf restores the flag bank after running real signed arithmetic. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitBaseline
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

 def flags (x : VertexRecord) : List Bool :=
  [x.probe,x.side,decide (x.track=x.cut.index),x.cut.leftRise,x.cut.rightRise,x.cut.leftDrop,x.cut.rightDrop]
 def flagPorts : List (Fin 23) := [16,17,18,19,20,21,22]
 def modeBits (bs : List Bool) : Mode :=
  if bs[0]?.getD false then .probe else if !(bs[1]?.getD false) then .even else
  if bs[2]?.getD false then
    if bs[3]?.getD false then .risePlus else if bs[4]?.getD false then .riseMinus else
    if bs[5]?.getD false then .dropMinus else if bs[6]?.getD false then .dropPlus else .ordinary
  else .ordinary
 lemma modeBits_flags (x : VertexRecord) : modeBits (flags x)=mode x := by
  simp [modeBits,flags,mode]

 def arithMap : Fin 16 ↪ Fin 23 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 23 => z.val) h)
 def store (R : Fin 7 → ℤ) (x : VertexRecord) (erased : ℕ) : Store 22 := fun i=>
  if h:i.val<16 then RegisterMachine.store [] [] (signedBits ∘ R) ⟨i.val,h⟩ else
  if erased=0 then [(flags x)[i.val-16]?.getD false] else []
 noncomputable def classify : OracleBlock 22 := skip
 noncomputable def leaf (bs : List Bool) : OracleBlock 22 :=
  seq (rename (compile (code (modeBits bs))) arithMap) (seedFlags (flagPorts.zip bs))
 noncomputable def choose : OracleBlock 22 := bitProgramChoice flagPorts leaf
 noncomputable def program : OracleBlock 22 := seq classify choose

 theorem classify_executes (g : BitString → ℕ) (R : Fin 7 → ℤ) (x : VertexRecord) :
    classify.Executes g (store R x 0) (store R x 0) 1 := skip_executes g _

 theorem choose_executes (g : BitString → ℕ) (R : Fin 7 → ℤ) (x : VertexRecord) (B : ℕ)
    (hR : Bounded B R) (hv : Valid (code (mode x)) R) :
    ∃t,choose.Executes g (store R x 0) (store (evaluate (code (mode x)) R) x 0) t ∧
      t≤(straightTime (code (mode x))).eval B+40 := by
  obtain ⟨t,ht,hb⟩ := compile_polynomial (code (mode x)) g R B hR hv
  have hc : (rename (compile (code (mode x))) arithMap).Executes g
      (store R x 1) (store (evaluate (code (mode x)) R) x 1) t := by
    apply rename_executes_to _ arithMap g ht
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have hn : ¬i.val<16 := by
        intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
      simp [store,hn]
  have hs : (seedFlags (flagPorts.zip (flags x))).Executes g
      (store (evaluate (code (mode x)) R) x 1) (store (evaluate (code (mode x)) R) x 0) 22 := by
    convert seedFlags_executes (flagPorts.zip (flags x)) g (store (evaluate (code (mode x)) R) x 1) using 1
    funext i;fin_cases i <;> rfl
  have hl : (leaf (flags x)).Executes g (store R x 1)
      (store (evaluate (code (mode x)) R) x 0) (t+22+2) := by
    unfold leaf
    rw [modeBits_flags]
    exact seq_executes _ _ g hc hs
  let bits : Fin 23 → Bool := fun i => (flags x)[i.val-16]?.getD false
  have hm : flagPorts.map bits=flags x := by rfl
  have he : eraseStore flagPorts (store R x 0)=store R x 1 := by
    funext i;fin_cases i <;> rfl
  have hp := bitProgramChoice_executes flagPorts (by decide) leaf bits g (store R x 0)
    (store (evaluate (code (mode x)) R) x 0) (by
      intro i hi;simp only [flagPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl) (t+22+2) (by simpa only [hm,he] using hl)
  exact ⟨_,hp,by simp only [flagPorts,List.length_cons,List.length_nil];omega⟩

 lemma program_queryFree : program.QueryFree := by
  apply seq_queryFree _ _ skip_queryFree
  apply bitProgramChoice_queryFree
  intro bs
  exact seq_queryFree _ _ (rename_queryFree _ _ (compile_queryFree _)) (seedFlags_queryFree _)
end HiddenCircuits.GraphReduction.Runtime.UnitBaseline
