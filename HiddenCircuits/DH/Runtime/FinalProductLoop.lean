import HiddenCircuits.DH.Runtime.FinalProductBody

/-! A real live-root loop, bounded from coefficient lengths and partial products. -/
namespace HiddenCircuits.DH.Runtime.FinalProduct
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

lemma while_executes (g : BitString→ℕ) (xs : Rows) (a B R : ℕ)
    (hne : ∀x∈xs,x.2≠[]) (hr : ∀x∈xs,(NumericEncoding.rowBits x.2).length≤R)
    (hB : ProductBitBound B (a:ℤ) (factors xs)) :
    ∃c,WhileExecution (0:Fin 14) body body g (loopStore xs a)
      (loopStore [] (a*product xs)) c ∧ c≤1+xs.length*(bodyBound B R+2) := by
  induction xs generalizing a with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa only [product,List.map_nil,List.prod_nil,Nat.mul_one] using
      WhileExecution.empty (loopStore [] a) rfl
  | cons x xs ih =>
    obtain ⟨b,row⟩:=x
    cases row with
    | nil => exact False.elim (hne (b,[]) List.mem_cons_self rfl)
    | cons x row =>
      have hB' : ProductBitBound B ((a*(if b then x else 1):ℕ):ℤ) (factors xs) := by
        simpa only [factors,List.map_cons,factor,CoefficientModel.read,List.getElem?_cons_zero,
          Option.getD_some,Nat.cast_mul,Nat.cast_ite,Nat.cast_one] using hB.2.2
      have hi:=ih (a*(if b then x else 1))
        (fun y hy=>hne y (List.mem_cons_of_mem _ hy))
        (fun y hy=>hr y (List.mem_cons_of_mem _ hy)) hB'
      obtain ⟨ct,ht,hbt⟩:=hi
      obtain ⟨cb,hb,hbb⟩:=body_executes g b x a B R row xs hB.head (hr _ List.mem_cons_self)
      have hup : Function.update (loopStore ((b,x::row)::xs) a) (0:Fin 14) (pairBits [b] (live xs))=
          store (pairBits [b] (live xs)) (table ((b,x::row)::xs)) [] [] (signedBits (a:ℤ)) [] := by
        funext i;fin_cases i <;> rfl
      have hw:=WhileExecution.one (s:=loopStore ((b,x::row)::xs) a) (rest:=pairBits [b] (live xs))
        (by rfl) (by rw [hup];exact hb) ht
      refine ⟨1+cb+1+ct,?_,?_⟩
      · simpa only [product_cons,CoefficientModel.read,List.getElem?_cons_zero,Option.getD_some,Nat.mul_assoc] using hw
      · simp only [List.length_cons];nlinarith

lemma loop_executes (g : BitString→ℕ) (xs : Rows) (a B R : ℕ)
    (hne : ∀x∈xs,x.2≠[]) (hr : ∀x∈xs,(NumericEncoding.rowBits x.2).length≤R)
    (hB : ProductBitBound B (a:ℤ) (factors xs)) :
    ∃c,loop.Executes g (loopStore xs a) (loopStore [] (a*product xs)) c ∧
      c≤1+xs.length*(bodyBound B R+2) := by
  obtain ⟨c,hc,hb⟩:=while_executes g xs a B R hne hr hB
  exact ⟨c,whilePop_executes _ _ _ g hc,hb⟩
lemma loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree
end HiddenCircuits.DH.Runtime.FinalProduct
