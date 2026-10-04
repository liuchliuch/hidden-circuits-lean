import HiddenCircuits.GraphReduction.Runtime.DescriptorRectangle
import HiddenCircuits.GraphReduction.Runtime.DescriptorMaskDifference

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorFront
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

def workState (v : VertexRecord) (width height samples clock : ℕ) (mask S T pairs out : BitString) (count : ℕ) (descriptor : BitString := []) : Store 19 := fun i =>
  if h:i.val<8 then DescriptorAtom.state v out count ⟨i.val,h⟩
  else if i.val=8 then List.replicate width true else if i.val=9 then mask
  else if i.val=10 then List.replicate height true else if i.val=11 then List.replicate clock true
  else if i.val=12 then S else if i.val=13 then T else if i.val=16 then pairs
  else if i.val=17 then List.replicate samples true else if i.val=18 then descriptor else []
def maskEmbedding : Fin 9 ↪ Fin 20 where
  toFun i := if h:i.val<8 then ⟨i.val,by omega⟩ else 9
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def rowEmbedding : Fin 11 ↪ Fin 20 where
  toFun i := (![0,1,2,3,4,5,6,7,9,8,19] : Fin 11 → Fin 20) i
  inj' := by decide +kernel

def rectangleEmbedding (probe : Bool) : Fin 13 ↪ Fin 20 where
  toFun i := (![0,1,2,3,4,5,6,7,9,(if probe then 17 else 8),19,10,11] : Fin 13 → Fin 20) i
  inj' := by cases probe <;> decide +kernel

def differenceEmbedding : Fin 4 ↪ Fin 20 where
  toFun i := (![14,15,19,9] : Fin 4 → Fin 20) i
  inj' := by decide +kernel

lemma rowEmbedding_low (i : Fin 8) : rowEmbedding ⟨i.val,by omega⟩=⟨i.val,by omega⟩ := by
  fin_cases i <;> rfl
lemma rectangleEmbedding_low (probe : Bool) (i : Fin 8) : (rectangleEmbedding probe) ⟨i.val,by omega⟩=⟨i.val,by omega⟩ := by
  cases probe <;> fin_cases i <;> rfl

noncomputable def maskRow : OracleBlock 19 := rename DescriptorMaskRow.program maskEmbedding
noncomputable def row : OracleBlock 19 := rename DescriptorRow.program rowEmbedding
noncomputable def rectangle (probe : Bool) : OracleBlock 19 := rename DescriptorRectangle.program (rectangleEmbedding probe)
noncomputable def rectangleLoop (probe : Bool) : OracleBlock 19 := rename DescriptorRectangle.loop (rectangleEmbedding probe)
noncomputable def difference : OracleBlock 19 := rename DescriptorMaskDifference.program differenceEmbedding

lemma maskRow_executes (g : BitString → ℕ) (v : VertexRecord) (hv : v.track=0) (width height samples clock : ℕ)
    (mask S T pairs out : BitString) (count : ℕ) :
    ∃c,maskRow.Executes g (workState v width height samples clock mask S T pairs out count)
      (workState v width height samples clock [] S T pairs
        ((encodeBitList ((DescriptorMaskRow.records v mask).map encodeVertex)).reverse++out)
        (count+(DescriptorMaskRow.records v mask).length)) c ∧
      c≤mask.length*(20*v.layer+20*mask.length+14*v.cut.index+120)+4 := by
  obtain ⟨c,hc,hb⟩ := DescriptorMaskRow.program_executes g v hv mask out count
  refine ⟨c,?_,hb⟩
  apply rename_executes_to DescriptorMaskRow.program maskEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hlow : ¬i.val<8 := by intro h;exact hi ⟨i.val,by omega⟩ (Fin.ext (by simp [maskEmbedding,h]))
    have h9 : i.val≠9 := by intro h;exact hi 8 (Fin.ext h.symm)
    simp only [workState,hlow,↓reduceDIte,h9,if_false]

lemma row_executes (g : BitString → ℕ) (v : VertexRecord) (hv : v.track=0) (width height samples clock : ℕ)
    (S T pairs out : BitString) (count : ℕ) :
    ∃c,row.Executes g (workState v width height samples clock [] S T pairs out count)
      (workState v width height samples clock [] S T pairs
        ((encodeBitList ((DescriptorRow.records v width).map encodeVertex)).reverse++out) (count+width)) c ∧
      c≤width*(20*v.layer+20*width+14*v.cut.index+125)+8 := by
  obtain ⟨c,hc,hb⟩ := DescriptorRow.program_executes g v hv width out count
  refine ⟨c,?_,hb⟩
  apply rename_executes_to DescriptorRow.program rowEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have hlow : ¬i.val<8 := by intro h;exact hi ⟨i.val,by omega⟩ (rowEmbedding_low ⟨i.val,h⟩)
    simp only [workState,hlow,↓reduceDIte]

lemma rectangle_executes (g : BitString → ℕ) (probe : Bool) (v : VertexRecord) (hv : v.track=0)
    (width height samples : ℕ) (S T pairs out : BitString) (count : ℕ) :
    ∃c,(rectangle probe).Executes g (workState v width height samples 0 [] S T pairs out count)
      (workState {v with layer:=v.layer+height} width height samples 0 [] S T pairs
        ((encodeBitList ((DescriptorRectangle.records v (if probe then samples else width) height).map encodeVertex)).reverse++out)
        (count+(if probe then samples else width)*height)) c ∧
      c≤height*((if probe then samples else width)*(20*(v.layer+height)+20*(if probe then samples else width)+14*v.cut.index+125)+18)+5 := by
  obtain ⟨c,hc,hb⟩ := DescriptorRectangle.program_executes g v hv (if probe then samples else width) height out count
  refine ⟨c,?_,hb⟩
  apply rename_executes_to DescriptorRectangle.program (rectangleEmbedding probe) g hc
  · funext i;cases probe <;> fin_cases i <;> rfl
  · funext i;cases probe <;> fin_cases i <;> rfl
  · intro i hi
    have hlow : ¬i.val<8 := by
      intro h
      exact hi ⟨i.val,by omega⟩ (rectangleEmbedding_low probe ⟨i.val,h⟩)
    simp only [workState,hlow,↓reduceDIte]

lemma rectangleLoop_executes (g : BitString → ℕ) (probe : Bool) (v : VertexRecord) (hv : v.track=0)
    (width height samples n : ℕ) (S T pairs out : BitString) (count : ℕ) :
    ∃c,(rectangleLoop probe).Executes g (workState v width height samples n [] S T pairs out count)
      (workState {v with layer:=v.layer+n} width height samples 0 [] S T pairs
        ((encodeBitList ((DescriptorRectangle.records v (if probe then samples else width) n).map encodeVertex)).reverse++out)
        (count+(if probe then samples else width)*n)) c ∧
      c≤n*((if probe then samples else width)*(20*(v.layer+n)+20*(if probe then samples else width)+14*v.cut.index+125)+13)+1 := by
  obtain ⟨c,hc,hb⟩ := DescriptorRectangle.loop_execution g v hv (if probe then samples else width) height n out count
  refine ⟨c,?_,hb⟩
  apply rename_executes_to DescriptorRectangle.loop (rectangleEmbedding probe) g (whilePop_executes _ _ _ g hc)
  · funext i;cases probe <;> fin_cases i <;> rfl
  · funext i;cases probe <;> fin_cases i <;> rfl
  · intro i hi
    have hlow : ¬i.val<8 := by
      intro h
      exact hi ⟨i.val,by omega⟩ (rectangleEmbedding_low probe ⟨i.val,h⟩)
    have h11 : i.val≠11 := by intro h;exact hi 12 (Fin.ext (by cases probe <;> exact h.symm))
    simp only [workState,hlow,↓reduceDIte,h11,if_false]

lemma difference_executes (g : BitString → ℕ) (v : VertexRecord) (width height samples clock : ℕ)
    (S T pairs out xs ys : BitString) (count : ℕ) (hlen : xs.length=ys.length) :
    difference.Executes g
      (Function.update (Function.update (workState v width height samples clock [] S T pairs out count) 14 xs) 15 ys)
      (workState v width height samples clock (DescriptorMaskDifference.difference xs ys) S T pairs out count) (7*xs.length+4) := by
  apply rename_executes_to DescriptorMaskDifference.program differenceEmbedding g (DescriptorMaskDifference.program_executes g xs ys hlen)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h14 : i≠14 := by intro h;subst i;exact hi 0 rfl
    have h15 : i≠15 := by intro h;subst i;exact hi 1 rfl
    have h9 : i.val≠9 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [Function.update_of_ne h15,Function.update_of_ne h14,workState,h9,if_false]
end HiddenCircuits.GraphReduction.Runtime.DescriptorFront
