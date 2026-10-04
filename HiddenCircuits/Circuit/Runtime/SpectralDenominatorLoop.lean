import HiddenCircuits.Circuit.Runtime.SpectralDenominatorCell

/-! Actual root-stream traversal with derived prefix-denominator bit bounds. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDenominator
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic IntegerSpectralWeights
open Polynomial

noncomputable def loop : OracleBlock 18 := whilePop 16 skip body
noncomputable def registerBound : Polynomial ℕ := (X+1)*X+2

theorem denominator_length (x : ℤ) (xs : List ℤ) (N : ℕ)
    (hx : (signedBits x).length≤N) (hxs : ∀a∈xs,(signedBits a).length≤N) (hlen : xs.length≤N) :
    (signedBits (denominator x xs)).length≤(N+1)*N+2 := by
  have hh := denominator_bit_bound x xs N (abs_le_pow_signed_length x N hx)
    (fun a ha => abs_le_pow_signed_length a N (hxs a ha))
  have hm := Nat.mul_le_mul_left (N+1) hlen
  simp only [signedBits,List.length_cons,encodeNat_length]
  omega

theorem loop_executes (g : BitString → ℕ) (x : ℤ) (todo done : List ℤ) (N : ℕ)
    (hx : (signedBits x).length≤N) (hlen : todo.length+done.length≤N)
    (htodo : ∀a∈todo,(signedBits a).length≤N) (hdone : ∀a∈done,(signedBits a).length≤N) :
    ∃ t, loop.Executes g (streamStore x (denominator x done) [] (signedBits 0) [] (encodeBitList (todo.map signedBits)))
      (streamStore x (denominator x (todo.reverse++done)) [] (signedBits 0) [] []) t ∧
      t≤todo.length*(bodyTime.eval ((N+1)*N+2)+2)+1 := by
  suffices ∃ t, WhileExecution (16:Fin 19) skip body g
      (streamStore x (denominator x done) [] (signedBits 0) [] (encodeBitList (todo.map signedBits)))
      (streamStore x (denominator x (todo.reverse++done)) [] (signedBits 0) [] []) t ∧
      t≤todo.length*(bodyTime.eval ((N+1)*N+2)+2)+1 by
    obtain ⟨t,ht,hb⟩ := this
    exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩
  induction todo generalizing done with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa [encodeBitList] using (WhileExecution.empty (stack:=(16:Fin 19)) (B:=skip) (C:=body)
      (g:=g) (streamStore x (denominator x done) [] (signedBits 0) [] []) rfl)
  | cons a todo ih =>
    have ha := htodo a (by simp)
    have ht' : ∀z∈todo,(signedBits z).length≤N := fun z hz => htodo z (by simp [hz])
    have hd' : ∀z∈a::done,(signedBits z).length≤N := by
      intro z hz;rcases List.mem_cons.mp hz with rfl|hz;exact ha;exact hdone z hz
    have hacc := denominator_length x done N hx hdone (by omega)
    have hx' : (signedBits x).length≤(N+1)*N+2 := by nlinarith
    have ha' : (signedBits a).length≤(N+1)*N+2 := by nlinarith
    obtain ⟨c,hc,hcb⟩ := body_executes g x (denominator x done) a (encodeBitList (todo.map signedBits))
      ((N+1)*N+2) (by omega) hx' hacc ha'
    have hden : denominator x done*(x-a)=denominator x (a::done) := by simp [denominator,mul_comm]
    rw [hden] at hc
    obtain ⟨t,ht,htb⟩ := ih (a::done) (by simp at hlen ⊢;omega) ht' hd'
    have he : Function.update
        (streamStore x (denominator x done) [] (signedBits 0) [] (encodeBitList ((a::todo).map signedBits))) (16:Fin 19)
        (pairBits (signedBits a) (encodeBitList (todo.map signedBits)))=
        streamStore x (denominator x done) [] (signedBits 0) [] (pairBits (signedBits a) (encodeBitList (todo.map signedBits))) := by
      funext i;fin_cases i <;> rfl
    rw [←he] at hc
    have hh := WhileExecution.one
      (show streamStore x (denominator x done) [] (signedBits 0) [] (encodeBitList ((a::todo).map signedBits)) 16=
        true::pairBits (signedBits a) (encodeBitList (todo.map signedBits)) from rfl) hc ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa [List.reverse_cons,List.append_assoc] using hh
    · simp only [List.length_cons]
      nlinarith

theorem loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ skip_queryFree body_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralDenominator
