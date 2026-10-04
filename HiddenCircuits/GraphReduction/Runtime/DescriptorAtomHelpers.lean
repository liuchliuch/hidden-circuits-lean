import HiddenCircuits.GraphReduction.Runtime.DescriptorAtomPure
import HiddenCircuits.Complexity.OracleRepeat

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorAtom
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def state (v : VertexRecord) (out : BitString) (count : ℕ) : Store 7 := fun i =>
  if i.val=0 then tagBits v else if i.val=1 then List.replicate v.layer true
  else if i.val=2 then List.replicate v.track true else if i.val=3 then List.replicate v.cut.index true
  else if i.val=4 then out else if i.val=5 then List.replicate count true else []

def payloadEmbedding : Fin 2 ↪ Fin 8 where
  toFun i := if i.val=0 then 6 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def tags : OracleBlock 7 := seq (copyOn 0 6 7 (by decide) (by decide) (by decide))
  (rename wordEmitLoop payloadEmbedding)

theorem tags_executes (oracle : BitString → ℕ) (v : VertexRecord) (out : BitString) (count : ℕ) :
    tags.Executes oracle (state v out count) (state v ((wordPayload (tagBits v)).reverse++out) count) 71 := by
  let s := Function.update (state v out count) (6:Fin 8) (tagBits v)
  have hc : (copyOn (0:Fin 8) 6 7 (by decide) (by decide) (by decide)).Executes oracle (state v out count) s 32 := by
    simpa [s,state,tagBits] using copyOn_executes oracle (0:Fin 8) 6 7 (by decide) (by decide) (by decide) (state v out count) rfl
  have hp : (rename wordEmitLoop payloadEmbedding).Executes oracle s
      (state v ((wordPayload (tagBits v)).reverse++out) count) 37 := by
    apply rename_executes_to wordEmitLoop payloadEmbedding oracle (wordEmitLoop_executes oracle (tagBits v) out)
    · funext i;fin_cases i <;> simp [s,state,payloadEmbedding,wordEmitStore] <;> rfl
    · funext i;fin_cases i <;> simp [state,payloadEmbedding,wordEmitStore] <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  exact seq_executes _ _ oracle hc hp

noncomputable def unary (source : Fin 8) (h6 : source≠6) (h7 : source≠7) (width : ℕ) : OracleBlock 7 :=
  seq (copyOn source 6 7 h6 h7 (by decide)) (repeatPrepend 6 4 (List.replicate width true))

theorem unary_executes (oracle : BitString → ℕ) (source : Fin 8) (h4 : source≠4) (h6 : source≠6) (h7 : source≠7)
    (width n : ℕ) (s : Store 7) (hs : s source=List.replicate n true) (hempty6 : s 6=[]) (hempty7 : s 7=[]) :
    (unary source h6 h7 width).Executes oracle s
      (Function.update s 4 (List.replicate (width*n) true++s 4)) ((3*width+8)*n+5) := by
  let s₁ := Function.update s (6:Fin 8) (List.replicate n true)
  have hc : (copyOn source 6 7 h6 h7 (by decide)).Executes oracle s s₁ (5*n+2) := by
    simpa [s₁,hs,hempty6] using copyOn_executes oracle source 6 7 h6 h7 (by decide) s hempty7
  have hh := repeatPrepend_executes oracle (6:Fin 8) 4 (by decide) (List.replicate width true) s₁
  have hr : (repeatPrepend (6:Fin 8) 4 (List.replicate width true)).Executes oracle s₁
      (Function.update s 4 (List.replicate (width*n) true++s 4)) ((3*width+3)*n+1) := by
    convert hh using 1
    · funext i
      by_cases h : i=6
      · subst i;simp [s₁,hempty6]
      · by_cases hi : i=4
        · subst i;simp [s₁,List.flatten_replicate_replicate,Nat.mul_comm]
        · simp [s₁,h,hi]
    · simp [s₁]
  convert seq_executes _ _ oracle hc hr using 1 <;> ring

theorem tags_queryFree : tags.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (rename_queryFree _ _ (whilePop_queryFree _ _ _
    (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
    (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))
theorem unary_queryFree (source : Fin 8) (h6 : source≠6) (h7 : source≠7) (width : ℕ) :
    (unary source h6 h7 width).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (repeatPrepend_queryFree _ _ _)
end HiddenCircuits.GraphReduction.Runtime.DescriptorAtom
