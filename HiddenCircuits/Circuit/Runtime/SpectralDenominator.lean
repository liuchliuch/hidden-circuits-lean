import HiddenCircuits.Circuit.Runtime.SpectralDenominatorLoop
import HiddenCircuits.Complexity.OracleRepeat
import HiddenCircuits.Complexity.OracleResult

/-! Full real polynomial-time Lagrange denominator computation on arbitrary integer nodes. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDenominator
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic IntegerSpectralWeights
open Polynomial

def rawStore (x roots : BitString) : Store 18 := fun i =>
  if i.val=9 then x else if i.val=16 then roots else []
noncomputable def constants : OracleBlock 18 :=
  seq (prepend 10 (signedBits 1)) (seq (prepend 12 (signedBits (-1)))
    (seq (push 13 false) (seq (push 14 false) (push 15 false))))
noncomputable def prepare : OracleBlock 18 :=
  seq (moveOn 0 9 2 (by decide) (by decide) (by decide))
    (seq (moveOn 1 16 2 (by decide) (by decide) (by decide)) constants)
noncomputable def work : OracleBlock 18 := seq prepare loop
noncomputable def program : OracleBlock 18 := seq work (cleanResult 10 2 (by decide) (by decide))
noncomputable def workTime : Polynomial ℕ := X*(bodyTime.comp registerBound+2)+6*X+42
noncomputable def time : Polynomial ℕ := 24*workTime+23*X+72

def inputLength (x : ℤ) (xs : List ℤ) : ℕ :=
  (signedBits x).length+(encodeBitList (xs.map signedBits)).length

theorem constants_executes (g : BitString → ℕ) (x : ℤ) (roots : BitString) :
    constants.Executes g (rawStore (signedBits x) roots) (streamStore x 1 [] (signedBits 0) [] roots) 25 := by
  let s₀ := rawStore (signedBits x) roots
  let s₁ := Function.update s₀ (10:Fin 19) (signedBits 1)
  let s₂ := Function.update s₁ (12:Fin 19) (signedBits (-1))
  let s₃ := Function.update s₂ (13:Fin 19) [false]
  let s₄ := Function.update s₃ (14:Fin 19) [false]
  let s₅ := Function.update s₄ (15:Fin 19) [false]
  have h₁ : (prepend (10:Fin 19) (signedBits 1)).Executes g s₀ s₁ 7 := by
    simpa [s₀,rawStore] using prepend_executes g (10:Fin 19) (signedBits 1) s₀
  have h₂ : (prepend (12:Fin 19) (signedBits (-1))).Executes g s₁ s₂ 7 := by
    simpa [s₁,s₀,rawStore] using prepend_executes g (12:Fin 19) (signedBits (-1)) s₁
  have h₃ : (push (13:Fin 19) false).Executes g s₂ s₃ 1 := push_executes g _ _ s₂
  have h₄ : (push (14:Fin 19) false).Executes g s₃ s₄ 1 := push_executes g _ _ s₃
  have h₅ : (push (15:Fin 19) false).Executes g s₄ s₅ 1 := push_executes g _ _ s₄
  have he : s₅=streamStore x 1 [] (signedBits 0) [] roots := by funext i;fin_cases i <;> rfl
  have hh := seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅)))
  rwa [he] at hh

theorem prepare_executes (g : BitString → ℕ) (x : ℤ) (roots : BitString) :
    prepare.Executes g (binaryStore (signedBits x) roots) (streamStore x 1 [] (signedBits 0) [] roots)
      (6*((signedBits x).length+roots.length)+39) := by
  let s₀ : Store 18 := binaryStore (signedBits x) roots
  let s₁ := Function.update (Function.update s₀ (9:Fin 19) (signedBits x)) (0:Fin 19) []
  let s₂ := rawStore (signedBits x) roots
  have h₁ : (moveOn (0:Fin 19) 9 2 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (6*(signedBits x).length+5) := by
    simpa [s₀,binaryStore] using moveOn_executes g (0:Fin 19) 9 2 (by decide) (by decide) (by decide) s₀ rfl
  have h₂ : (moveOn (1:Fin 19) 16 2 (by decide) (by decide) (by decide)).Executes g s₁ s₂ (6*roots.length+5) := by
    convert moveOn_executes g (1:Fin 19) 16 2 (by decide) (by decide) (by decide) s₁ rfl using 1
    funext i;fin_cases i <;> simp [s₁,s₀,s₂,binaryStore,rawStore]
  have h₃ := constants_executes g x roots
  convert seq_executes _ _ g h₁ (seq_executes _ _ g h₂ h₃) using 1 <;> omega

theorem work_executes (g : BitString → ℕ) (x : ℤ) (xs : List ℤ) :
    ∃ t, work.Executes g (binaryStore (signedBits x) (encodeBitList (xs.map signedBits)))
      (streamStore x (denominator x xs) [] (signedBits 0) [] []) t ∧ t≤workTime.eval (inputLength x xs) := by
  let N := inputLength x xs
  have hx : (signedBits x).length≤N := by unfold N inputLength;omega
  have hlen : xs.length≤N := by
    have h := list_length_le_encodeBitList_length (xs.map signedBits)
    simp only [List.length_map] at h
    unfold N inputLength;omega
  have hxs : ∀a∈xs,(signedBits a).length≤N := by
    intro a ha
    have h := member_length_le_encodeBitList (List.mem_map.mpr ⟨a,ha,rfl⟩ : signedBits a∈xs.map signedBits)
    unfold N inputLength;omega
  have hi := prepare_executes g x (encodeBitList (xs.map signedBits))
  obtain ⟨t,ht,htb⟩ := loop_executes g x xs [] N hx (by simpa using hlen) hxs (by simp)
  have hd : denominator x xs.reverse=denominator x xs := by simp [denominator,List.map_reverse,List.prod_reverse]
  simp only [List.append_nil,hd,show denominator x []=1 from rfl] at ht
  refine ⟨6*N+39+t+2,seq_executes _ _ g hi ht,?_⟩
  have hm := Nat.mul_le_mul_right (bodyTime.eval ((N+1)*N+2)+2) hlen
  simp only [workTime,registerBound,eval_add,eval_mul,eval_comp,eval_X,eval_one,eval_ofNat]
  change 6*N+39+t+2≤N*(bodyTime.eval ((N+1)*N+2)+2)+6*N+42
  omega

/-- Canonical signed x and root words produce the exact signed product, with
all auxiliary tapes empty and unconditional polynomial charged runtime. -/
theorem program_executes (g : BitString → ℕ) (x : ℤ) (xs : List ℤ) :
    ∃ t, program.Executes g (binaryStore (signedBits x) (encodeBitList (xs.map signedBits)))
      (binaryStore (signedBits (denominator x xs)) []) t ∧ t≤time.eval (inputLength x xs) := by
  obtain ⟨c,hc,hcb⟩ := work_executes g x xs
  obtain ⟨d,hd,hdb⟩ := cleanResult_executes g (10:Fin 19) 2 (by decide) (by decide) (by decide)
    (streamStore x (denominator x xs) [] (signedBits 0) [] []) (inputLength x xs+c)
    (hc.stack_bound (binaryStore_bound _ _))
  have he : Function.update (fun _ : Fin 19 => ([]:BitString)) 0 (signedBits (denominator x xs))=
      binaryStore (signedBits (denominator x xs)) [] := by funext i;fin_cases i <;> rfl
  change (cleanResult (10:Fin 19) 2 (by decide) (by decide)).Executes g _
    (Function.update (fun _ : Fin 19 => ([]:BitString)) 0 (signedBits (denominator x xs))) d at hd
  rw [he] at hd
  refine ⟨c+d+2,seq_executes _ _ g hc hd,?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (prepend_queryFree _ _) (seq_queryFree _ _ (prepend_queryFree _ _)
          (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)))))))
    loop_queryFree) (cleanResult_queryFree _ _ _ _)

noncomputable def programOn {k : ℕ} (φ : Fin 19 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 19 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (x : ℤ) (xs : List ℤ) (hs : s∘φ=binaryStore (signedBits x) (encodeBitList (xs.map signedBits))) :
    ∃ t, (programOn φ).Executes g s
      (Function.update (Function.update s (φ 0) (signedBits (denominator x xs))) (φ 1) []) t ∧
      t≤time.eval (inputLength x xs) := by
  obtain ⟨t,ht,hb⟩ := program_executes g x xs
  exact ⟨t,rename_binary_executes program φ g s _ _ _ t ht hs,hb⟩

theorem programOn_queryFree {k : ℕ} (φ : Fin 19 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralDenominator
