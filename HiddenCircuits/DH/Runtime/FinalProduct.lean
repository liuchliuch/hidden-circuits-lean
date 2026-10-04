import HiddenCircuits.DH.Runtime.FinalProductLoop

/-! Clean14-port final product: literal initialization, live-root loop and unsigned output. -/
namespace HiddenCircuits.DH.Runtime.FinalProduct
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 800000

def output (z : ℕ) : Store 13 := store (Computability.encodeNat z) [] [] [] [] []
noncomputable def strip : OracleBlock 13 := branchPop 4 skip skip skip
noncomputable def finish : OracleBlock 13 := seq strip (moveOn 4 0 5 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 13 := seq (prepend 4 [false,true]) (seq loop finish)

lemma finish_executes (g : BitString→ℕ) (z : ℕ) :
    finish.Executes g (loopStore [] z) (output z) (6*(Computability.encodeNat z).length+10) := by
  have hs : strip.Executes g (loopStore [] z)
      (store [] [] [] [] (Computability.encodeNat z) []) 3 := by
    apply branchPop_false 4 _ _ _ g (rest:=Computability.encodeNat z)
    · exact NumericEncoding.positive_word z
    · convert skip_executes g (store [] [] [] [] (Computability.encodeNat z) []) using 1
      funext i;fin_cases i <;> rfl
  have hm : (moveOn (4:Fin 14) 0 5 (by decide) (by decide) (by decide)).Executes g
      (store [] [] [] [] (Computability.encodeNat z) []) (output z)
      (6*(Computability.encodeNat z).length+5) := by
    convert moveOn_executes g (4:Fin 14) 0 5 (by decide) (by decide) (by decide)
      (store [] [] [] [] (Computability.encodeNat z) []) rfl using 1
    funext i;fin_cases i <;> simp [store,output]
  convert seq_executes _ _ g hs hm using 1 <;> omega

lemma bound_final (xs : Rows) (a B : ℕ) (hB : ProductBitBound B (a:ℤ) (factors xs)) :
    (signedBits ((a*product xs:ℕ):ℤ)).length≤B := by
  induction xs generalizing a with
  | nil => simpa only [product,List.map_nil,List.prod_nil,Nat.mul_one] using hB
  | cons x xs ih =>
    have ht : ProductBitBound B ((a*factor x:ℕ):ℤ) (factors xs) := by
      simpa only [factors,List.map_cons,Nat.cast_mul] using hB.2.2
    have hi:=ih (a*factor x) ht
    simpa only [product,List.map_cons,List.prod_cons,Nat.mul_assoc] using hi

lemma program_executes (g : BitString→ℕ) (xs : Rows) (B R : ℕ)
    (hne : ∀x∈xs,x.2≠[]) (hr : ∀x∈xs,(NumericEncoding.rowBits x.2).length≤R)
    (hB : ProductBitBound B 1 (factors xs)) :
    ∃c,program.Executes g (initial (live xs) (table xs)) (output (product xs)) c ∧
      c≤xs.length*(bodyBound B R+2)+6*B+22 := by
  have hp : (prepend (4:Fin 14) [false,true]).Executes g (initial (live xs) (table xs)) (loopStore xs 1) 7 := by
    convert prepend_executes g (4:Fin 14) [false,true] (initial (live xs) (table xs)) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hc,hb⟩:=loop_executes g xs 1 B R hne hr hB
  simp only [Nat.one_mul] at hc
  have hf:=finish_executes g (product xs)
  have hz:=bound_final xs 1 B hB
  simp only [Nat.one_mul,NumericEncoding.positive_word,List.length_cons] at hz
  refine ⟨7+(c+(6*(Computability.encodeNat (product xs)).length+10)+2)+2,?_,by omega⟩
  exact seq_executes _ _ g hp (seq_executes _ _ g hc hf)

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (seq_queryFree _ _ (seq_queryFree _ _ skip_queryFree (push_queryFree _ _)) (push_queryFree _ _))
  (seq_queryFree _ _ loop_queryFree (seq_queryFree _ _
    (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree skip_queryFree)
    (moveOn_queryFree _ _ _ _ _ _)))
noncomputable def on {k : ℕ} (φ : Fin 14 ↪ Fin (k+1)) : OracleBlock k := rename program φ
lemma on_queryFree {k : ℕ} (φ : Fin 14 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.DH.Runtime.FinalProduct
