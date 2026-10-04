import HiddenCircuits.Complexity.BinaryArithmetic.Factorial
import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits
import HiddenCircuits.Complexity.OracleMove

/-! A framed factorial producer for the numeric-table machine. Unary index
words are preserved; the result is canonical signed magnitude for direct
composition with the verified integer-operation blocks. -/
namespace HiddenCircuits.DH.Runtime.FactorialInto
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic
open Polynomial

 def state (source output : BitString) (work : Store 6) : Store 8 := fun i=>
  if i.val=0 then source else if i.val=1 then output else work ⟨i.val-2,by omega⟩
 def store (source output : BitString) : Store 8 := state source output (fun _=>[])
 def embedding : Fin 7↪Fin 9 where
  toFun i:=⟨i.val+2,by omega⟩
  inj':=by intro i j h;apply Fin.ext;have he:=congrArg Fin.val h;dsimp at he;omega

 noncomputable def compute : OracleBlock 8 := rename factorialBlock embedding
 noncomputable def program : OracleBlock 8 :=
  seq (copyOn 0 2 3 (by decide) (by decide) (by decide))
    (seq compute (seq (push 2 false) (moveOn 2 1 3 (by decide) (by decide) (by decide))))

 lemma signed_nat (m : ℕ) : signedBits (m:ℤ)=false::Computability.encodeNat m := by
  simp [signedBits,negative]

 noncomputable def time : Polynomial ℕ := factorialTime+6*X^2+5*X+26

 theorem executes (g : BitString→ℕ) (source : BitString) :
    ∃t, program.Executes g (store source []) (store source (signedBits (source.length.factorial:ℤ))) t ∧
      t≤time.eval source.length := by
  let word := Computability.encodeNat source.length.factorial
  let signed := signedBits (source.length.factorial:ℤ)
  let startWork := factorialStore source [] [] [] [] [] []
  let endWork := factorialStore word [] [] [] [] [] []
  let signWork := factorialStore signed [] [] [] [] [] []
  have hcopy : (copyOn (0:Fin 9) 2 3 (by decide) (by decide) (by decide)).Executes g
      (store source []) (state source [] startWork) (5*source.length+2) := by
    convert copyOn_executes g (0:Fin 9) 2 3 (by decide) (by decide) (by decide) (store source []) rfl using 1
    funext i;fin_cases i <;> simp [state,store,startWork,factorialStore]
  obtain ⟨t,ht,hbound⟩ := factorial_polynomial g source
  have hcompute : compute.Executes g (state source [] startWork) (state source [] endWork) t := by
    apply rename_executes_to factorialBlock embedding g ht
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | exact False.elim (hi 4 rfl) | exact False.elim (hi 5 rfl) | exact False.elim (hi 6 rfl)

  have hsign : (push (2:Fin 9) false).Executes g (state source [] endWork) (state source [] signWork) 1 := by
    convert push_executes g (2:Fin 9) false (state source [] endWork) using 1
    funext i;fin_cases i <;> simp [state,endWork,signWork,factorialStore,signed,word,signed_nat]
  have hmove : (moveOn (2:Fin 9) 1 3 (by decide) (by decide) (by decide)).Executes g
      (state source [] signWork) (store source signed) (6*signed.length+5) := by
    convert moveOn_executes g (2:Fin 9) 1 3 (by decide) (by decide) (by decide) (state source [] signWork) rfl using 1
    funext i;fin_cases i <;> simp [store,state,signWork,factorialStore]
  have hall := seq_executes _ _ g hcopy (seq_executes _ _ g hcompute (seq_executes _ _ g hsign hmove))
  refine ⟨_,hall,?_⟩
  have hs : signed.length≤source.length*source.length+2 := by
    have h := factorial_binary_length source.length
    simp only [signed,signed_nat,List.length_cons]
    omega
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
  nlinarith

 lemma queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _
    (rename_queryFree _ _ factorialBlock_queryFree)
      (seq_queryFree _ _ (push_queryFree _ _) (moveOn_queryFree _ _ _ _ _ _)))

 noncomputable def on {k : ℕ} (φ : Fin 9↪Fin (k+1)) : OracleBlock k := rename program φ

 theorem on_executes {k : ℕ} (φ : Fin 9↪Fin (k+1)) (g : BitString→ℕ) (s : Store k)
    (source : BitString) (hs : s∘φ=store source []) :
    ∃t, (on φ).Executes g s (Function.update s (φ 1) (signedBits (source.length.factorial:ℤ))) t ∧
      t≤time.eval source.length := by
  obtain ⟨t,ht,hb⟩ := executes g source
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 1) (signedBits (source.length.factorial:ℤ)))∘φ=
        Function.update (s∘φ) 1 (signedBits (source.length.factorial:ℤ)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 1).symm _ _

 lemma on_queryFree {k : ℕ} (φ : Fin 9↪Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ queryFree

end HiddenCircuits.DH.Runtime.FactorialInto
