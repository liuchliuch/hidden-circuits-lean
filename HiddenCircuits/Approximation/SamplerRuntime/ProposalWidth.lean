import HiddenCircuits.Complexity.BinaryArithmetic.UnaryBinary
import HiddenCircuits.Complexity.GraphVerifier.HeaderStage

/-! Compute the proposal bit width by real unary-to-binary increments and length scan. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.ProposalWidth
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic GraphVerifier.Runtime

def state (input clock width binary temporary flag : BitString) : Store 5 := fun r =>
  if r.val=0 then input else if r.val=1 then clock else if r.val=2 then width
  else if r.val=3 then binary else if r.val=4 then temporary else flag

def binaryMap : Fin 3 ↪ Fin 6 where
  toFun i := ![1,3,4] i
  inj' := by decide +kernel
def headerMap : Fin 4 ↪ Fin 6 where
  toFun i := ![3,2,4,5] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 5 := seq (copyOn 0 1 4 (by decide) (by decide) (by decide))
  (seq (rename unaryBinary binaryMap) (seq (headerOn headerMap) (seq (clear 3) (clear 5))))

theorem program_executes (g : BitString → ℕ) (input : BitString) :
    ∃t,program.Executes g (state input [] [] [] [] [])
      (state input [] (List.replicate (Nat.size input.length) true) [] [] []) t ∧
      t≤40*(input.length+1)^2 := by
  let bs := Computability.encodeNat input.length
  have h1 : (copyOn (0:Fin 6) 1 4 (by decide) (by decide) (by decide)).Executes g
      (state input [] [] [] [] []) (state input input [] [] [] []) (5*input.length+2) := by
    convert copyOn_executes g (0:Fin 6) 1 4 (by decide) (by decide) (by decide) (state input [] [] [] [] []) rfl using 1
    funext r;fin_cases r <;> simp [state]
  have h2 : (rename unaryBinary binaryMap).Executes g (state input input [] [] [] [])
      (state input [] [] bs [] []) (unaryBinaryCost 0 input.length) := by
    apply rename_executes_to unaryBinary binaryMap g (unaryBinary_executes g input 0)
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> simp [state,binaryMap,unaryBinaryStore,bs]
    · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 1 rfl)
  have h3 : (headerOn headerMap).Executes g (state input [] [] bs [] [])
      (state input [] (List.replicate bs.length true) bs [] [bs.all id]) (5*bs.length+3) := by
    convert headerOn_executes headerMap g (state input [] [] bs [] []) bs
      (by funext r;fin_cases r <;> rfl) using 1
    funext r;fin_cases r <;> rfl
  have h4 : (clear (3:Fin 6)).Executes g (state input [] (List.replicate bs.length true) bs [] [bs.all id])
      (state input [] (List.replicate bs.length true) [] [] [bs.all id]) (bs.length+1) := by
    convert clear_executes g (3:Fin 6) _ using 1
    funext r;fin_cases r <;> rfl
  have h5 : (clear (5:Fin 6)).Executes g (state input [] (List.replicate bs.length true) [] [] [bs.all id])
      (state input [] (List.replicate bs.length true) [] [] []) 2 := by
    convert clear_executes g (5:Fin 6) _ using 1
    funext r;fin_cases r <;> rfl
  have h := seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5)))
  have hlen : bs.length=Nat.size input.length := encodeNat_length _
  refine ⟨5*input.length+2+(unaryBinaryCost 0 input.length+(5*bs.length+3+(bs.length+1+2+2)+2)+2)+2,?_,?_⟩
  · convert h using 1
    rw [hlen]
  · have hc := unaryBinaryCost_le input.length 0 input.length (by omega)
    have hs : bs.length ≤ input.length := hlen.le.trans (Nat.size_le.mpr Nat.lt_two_pow_self)
    nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ unaryBinary_queryFree) (seq_queryFree _ _ (headerOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))
noncomputable def on {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k) (input : BitString)
    (hs : s∘φ=state input [] [] [] [] []) :
    ∃t,(on φ).Executes g s (Function.update s (φ 2) (List.replicate (Nat.size input.length) true)) t ∧
      t≤40*(input.length+1)^2 := by
  obtain ⟨t,ht,hb⟩ := program_executes g input
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 2) (List.replicate (Nat.size input.length) true))∘φ=
        Function.update (s∘φ) 2 (List.replicate (Nat.size input.length) true) := by
      funext r;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext r;fin_cases r <;> rfl
  · intro r hr;exact Function.update_of_ne (hr 2).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.Approximation.SamplerRuntime.ProposalWidth
