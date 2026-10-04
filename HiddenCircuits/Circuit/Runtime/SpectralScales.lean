import HiddenCircuits.Circuit.Runtime.SpectralScalesLoop
import HiddenCircuits.Complexity.OracleResult

/-! Clean polynomial bit program for all exact common-denominator row scales. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralScales
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

def inputStore (scale left right : BitString) : Store 20 := fun i =>
  if i.val=0 then scale else if i.val=1 then left else if i.val=2 then right else []
def rawStore (scale left right : BitString) : Store 20 := fun i =>
  if i.val=9 then scale else if i.val=16 then left else if i.val=20 then right else []
noncomputable def constants : OracleBlock 20 := seq (push 13 false) (seq (push 14 false) (push 15 false))
noncomputable def prepare : OracleBlock 20 := seq (moveOn 0 9 3 (by decide) (by decide) (by decide))
  (seq (moveOn 1 16 3 (by decide) (by decide) (by decide))
    (seq (moveOn 2 20 3 (by decide) (by decide) (by decide)) constants))
noncomputable def work : OracleBlock 20 := seq prepare (seq loop (reverseOn 17 16 (by decide)))
noncomputable def program : OracleBlock 20 := seq work (cleanResult 16 3 (by decide) (by decide))
noncomputable def workTime : Polynomial ℕ := X*(bodyTime+2)+6*X+4*X*(4*X+10)+34
noncomputable def time : Polynomial ℕ := 26*workTime+25*X+78

def inputLength (scale : ℤ) (ps : List (ℤ×ℤ)) : ℕ := (signedBits scale).length+
  (encodeBitList (ps.map (fun p => signedBits p.1))).length+(encodeBitList (ps.map (fun p => signedBits p.2))).length

theorem constants_executes (g : BitString → ℕ) (scale : ℤ) (left right : BitString) :
    constants.Executes g (rawStore (signedBits scale) left right) (store scale [] [] [] [] left right []) 7 := by
  let s₀ := rawStore (signedBits scale) left right
  let s₁ := Function.update s₀ (13:Fin 21) [false]
  let s₂ := Function.update s₁ (14:Fin 21) [false]
  let s₃ := Function.update s₂ (15:Fin 21) [false]
  have h₁ : (push (13:Fin 21) false).Executes g s₀ s₁ 1 := push_executes g _ _ s₀
  have h₂ : (push (14:Fin 21) false).Executes g s₁ s₂ 1 := push_executes g _ _ s₁
  have h₃ : (push (15:Fin 21) false).Executes g s₂ s₃ 1 := push_executes g _ _ s₂
  have he : s₃=store scale [] [] [] [] left right [] := by funext i;fin_cases i <;> rfl
  have hh := seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃)
  rwa [he] at hh

theorem prepare_executes (g : BitString → ℕ) (scale : ℤ) (left right : BitString) :
    prepare.Executes g (inputStore (signedBits scale) left right) (store scale [] [] [] [] left right [])
      (6*((signedBits scale).length+left.length+right.length)+28) := by
  let s₀ := inputStore (signedBits scale) left right
  let s₁ := Function.update (Function.update s₀ (9:Fin 21) (signedBits scale)) (0:Fin 21) []
  let s₂ := Function.update (Function.update s₁ (16:Fin 21) left) (1:Fin 21) []
  let s₃ := rawStore (signedBits scale) left right
  have h₁ : (moveOn (0:Fin 21) 9 3 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (6*(signedBits scale).length+5) := by
    simpa [s₀,inputStore] using moveOn_executes g (0:Fin 21) 9 3 (by decide) (by decide) (by decide) s₀ rfl
  have h₂ : (moveOn (1:Fin 21) 16 3 (by decide) (by decide) (by decide)).Executes g s₁ s₂ (6*left.length+5) := by
    simpa [s₁,s₀,inputStore] using moveOn_executes g (1:Fin 21) 16 3 (by decide) (by decide) (by decide) s₁ rfl
  have h₃ : (moveOn (2:Fin 21) 20 3 (by decide) (by decide) (by decide)).Executes g s₂ s₃ (6*right.length+5) := by
    convert moveOn_executes g (2:Fin 21) 20 3 (by decide) (by decide) (by decide) s₂ rfl using 1
    funext i;fin_cases i <;> simp [s₂,s₁,s₀,s₃,inputStore,rawStore]
  have h₄ := constants_executes g scale left right
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ h₄)) using 1 <;> omega

theorem work_executes (g : BitString → ℕ) (scale : ℤ) (ps : List (ℤ×ℤ))
    (hvalid : ∀p∈ps,p.1≠0 ∧ p.1∣scale) :
    ∃ t, work.Executes g (inputStore (signedBits scale) (encodeBitList (ps.map (fun p => signedBits p.1)))
        (encodeBitList (ps.map (fun p => signedBits p.2))))
      (store scale [] [] [] [] (encodeBitList ((output scale ps).map signedBits)) [] []) t ∧
      t≤workTime.eval (inputLength scale ps) := by
  let N := inputLength scale ps
  let out := encodeBitList ((output scale ps).map signedBits)
  have hs : (signedBits scale).length≤N := by unfold N inputLength;omega
  have hp : ∀p∈ps,(signedBits p.1).length≤N ∧ (signedBits p.2).length≤N := by
    intro p hp
    have h₁ := member_length_le_encodeBitList (List.mem_map.mpr ⟨p,hp,rfl⟩ : signedBits p.1∈ps.map (fun p => signedBits p.1))
    have h₂ := member_length_le_encodeBitList (List.mem_map.mpr ⟨p,hp,rfl⟩ : signedBits p.2∈ps.map (fun p => signedBits p.2))
    unfold N inputLength;omega
  have hn : ps.length≤N := by
    have h := list_length_le_encodeBitList_length (ps.map (fun p => signedBits p.1))
    simp only [List.length_map] at h
    unfold N inputLength;omega
  have hi := prepare_executes g scale (encodeBitList (ps.map (fun p => signedBits p.1)))
    (encodeBitList (ps.map (fun p => signedBits p.2)))
  obtain ⟨t,ht,htb⟩ := loop_executes g scale ps [] N hs hp hvalid
  simp only [List.append_nil] at ht
  have hf : (reverseOn (17:Fin 21) 16 (by decide)).Executes g (store scale [] [] [] [] [] [] out.reverse)
      (store scale [] [] [] [] out [] []) (2*out.length+1) := by
    convert reverseOn_executes g (17:Fin 21) 16 (by decide) (store scale [] [] [] [] [] [] out.reverse) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  refine ⟨(6*N+28)+(t+(2*out.length+1)+2)+2,seq_executes _ _ g hi (seq_executes _ _ g ht hf),?_⟩
  have ho := output_stream_bound scale ps N hs hp
  have hm := Nat.mul_le_mul_right (bodyTime.eval N+2) hn
  have hn' := Nat.mul_le_mul_right (8*N+20) hn
  simp only [workTime,eval_add,eval_mul,eval_X,eval_ofNat]
  change _≤N*(bodyTime.eval N+2)+6*N+4*N*(4*N+10)+34
  dsimp [out]
  nlinarith

theorem program_executes (g : BitString → ℕ) (scale : ℤ) (ps : List (ℤ×ℤ))
    (hvalid : ∀p∈ps,p.1≠0 ∧ p.1∣scale) :
    ∃ t, program.Executes g (inputStore (signedBits scale) (encodeBitList (ps.map (fun p => signedBits p.1)))
        (encodeBitList (ps.map (fun p => signedBits p.2))))
      (Function.update (fun _ : Fin 21 => ([]:BitString)) 0 (encodeBitList ((output scale ps).map signedBits))) t ∧
      t≤time.eval (inputLength scale ps) := by
  obtain ⟨c,hc,hcb⟩ := work_executes g scale ps hvalid
  have hs : ∀i, ((inputStore (signedBits scale) (encodeBitList (ps.map (fun p => signedBits p.1)))
        (encodeBitList (ps.map (fun p => signedBits p.2)))) i).length≤ inputLength scale ps := by
    intro i;unfold inputStore;split_ifs <;> unfold inputLength <;> (try simp only [List.length_nil]) <;> omega
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes g (16:Fin 21) 3 (by decide) (by decide) (by decide)
    (store scale [] [] [] [] (encodeBitList ((output scale ps).map signedBits)) [] [])
    (inputLength scale ps+c) (hc.stack_bound hs)
  refine ⟨c+d+2,seq_executes _ _ g hc hd,?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
          (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))))))
    (seq_queryFree _ _ loop_queryFree (reverseOn_queryFree _ _ _))) (cleanResult_queryFree _ _ _ _)
end HiddenCircuits.Circuit.Runtime.SpectralScales
