import HiddenCircuits.Circuit.Runtime.SpectralTableLoop
import HiddenCircuits.Complexity.CNFCloneEmitter.Dimensions

/-! Real spectral node counting supplies the basis-table loop clock. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTable
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

 def nodeWords (g : ℕ) : List BitString := ((spectralIndices g).map spectralIntegerNode).map signedBits
 def nodeCount (g : ℕ) : ℕ := (spectralIndices g).length

 theorem nodeWords_length (g : ℕ) : (nodeWords g).length=nodeCount g := by simp [nodeWords,nodeCount]
 theorem nodeWords_stream_length (g : ℕ) : (encodeBitList (nodeWords g)).length≤SpectralFrontend.streamBound.eval g := by
  have h := SpectralNodes.triangle_stream_length (g+1)
  rw [SpectralNodes.triangle_spectral] at h
  simpa only [nodeWords,SpectralFrontend.streamBound,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat,pow_two] using h
 theorem nodeCount_bound (g : ℕ) : nodeCount g≤(g+1)^2 := by
  rw [nodeCount,spectralIndices_length]
  exact spectralIndex_card_bound g

 def nodesEmbedding : Fin 13 ↪ Fin 33 where
  toFun i := frontendEmbedding i.castSucc
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 14 => z.val) (frontendEmbedding.injective h))
 def countEmbedding : Fin 8 ↪ Fin 33 where
  toFun i := if i.val=0 then 7 else if i.val=1 then 8 else if i.val=2 then 9 else if i.val=3 then 10
    else if i.val=4 then 11 else if i.val=5 then 5 else if i.val=6 then 2 else 12
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def initializeTable : OracleBlock 32 := seq (rename SpectralNodes.program nodesEmbedding)
  (seq (rename CNFCloneEmitter.countLoop countEmbedding) (copyOn 2 32 7 (by decide) (by decide) (by decide)))
noncomputable def initTime : Polynomial ℕ := SpectralNodes.time+15*SpectralFrontend.streamBound+5*(X+1)^2+7

theorem initializeTable_executes (oracle : BitString → ℕ) (g : ℕ) :
    ∃ t, initializeTable.Executes oracle (state g 0 [] [] [] [] [] [] [] [])
      (state g 0 (List.replicate (nodeCount g) true) [] [] [] [] [] [] (List.replicate (nodeCount g) true)) t ∧
      t≤ initTime.eval g := by
  let s₀ := state g 0 [] [] [] [] [] [] [] []
  let s₁ := state g 0 [] (encodeBitList (nodeWords g)) [] [] [] [] [] []
  let s₂ := state g 0 (List.replicate (nodeCount g) true) [] [] [] [] [] [] []
  let s₃ := state g 0 (List.replicate (nodeCount g) true) [] [] [] [] [] [] (List.replicate (nodeCount g) true)
  obtain ⟨a,ha,hab⟩ := SpectralNodes.program_executes oracle g
  have h₁ : (rename SpectralNodes.program nodesEmbedding).Executes oracle s₀ s₁ a := by
    apply rename_executes_to SpectralNodes.program nodesEmbedding oracle ha
    · funext i;fin_cases i <;> simp [s₀,state,nodesEmbedding,frontendEmbedding,SpectralNodes.inputStore]
    · funext i;fin_cases i <;> simp [s₁,state,nodesEmbedding,frontendEmbedding,SpectralNodes.outputStore,SpectralNodes.inputStore,nodeWords]
    · intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 0 rfl)
  have h₂ : (rename CNFCloneEmitter.countLoop countEmbedding).Executes oracle s₁ s₂
      (6*((nodeWords g).map List.length).sum+15*(nodeWords g).length+1) := by
    have hh := CNFCloneEmitter.countLoop_executes oracle [] [] [] (nodeWords g)
    apply rename_executes_to CNFCloneEmitter.countLoop countEmbedding oracle hh
    · funext i;fin_cases i <;> rfl
    · rw [nodeWords_length]
      funext i;fin_cases i <;> rfl
    · intro j hj;fin_cases j <;> first | rfl | exact False.elim (hj 5 rfl) | exact False.elim (hj 6 rfl)
  have h₃ : (copyOn (2:Fin 33) 32 7 (by decide) (by decide) (by decide)).Executes oracle s₂ s₃ (5*nodeCount g+2) := by
    convert copyOn_executes oracle (2:Fin 33) 32 7 (by decide) (by decide) (by decide) s₂ rfl using 1
    · funext i;fin_cases i <;> simp [s₂,s₃,state]
    · simp [s₂,state]
  have hc : 6*((nodeWords g).map List.length).sum+15*(nodeWords g).length+1≤15*(encodeBitList (nodeWords g)).length+1 := by
    rw [encodeBitList_length]
    omega
  have hn := nodeCount_bound g
  have hs := nodeWords_stream_length g
  refine ⟨a+((6*((nodeWords g).map List.length).sum+15*(nodeWords g).length+1)+(5*nodeCount g+2)+2)+2,
    seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ h₃),?_⟩
  simp only [initTime,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  omega

theorem initializeTable_queryFree : initializeTable.QueryFree := by
  have hb : CNFCloneEmitter.countBody.QueryFree := seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
  have hc : CNFCloneEmitter.countLoop.QueryFree := whilePop_queryFree _ _ _ hb hb
  exact seq_queryFree _ _ (rename_queryFree _ _ SpectralNodes.program_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ hc) (copyOn_queryFree _ _ _ _ _ _))

noncomputable def reverseInPlace {k : ℕ} (p q r : Fin (k+1)) (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) : OracleBlock k :=
  seq (reverseOn p q hpq) (moveOn q p r hpq.symm hqr hpr)

theorem reverseInPlace_executes {k : ℕ} (oracle : BitString → ℕ) (p q r : Fin (k+1))
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (s : Store k) (hq : s q=[]) (hr : s r=[]) :
    (reverseInPlace p q r hpq hpr hqr).Executes oracle s (Function.update s p (s p).reverse) (8*(s p).length+8) := by
  let t := Function.update (Function.update s p []) q (s p).reverse
  have h₁ : (reverseOn p q hpq).Executes oracle s t (2*(s p).length+1) := by
    simpa [hq] using reverseOn_executes oracle p q hpq s
  have htemp : t r=[] := by simp [t,hqr.symm,hpr.symm,hr]
  have hh := moveOn_executes oracle q p r hpq.symm hqr hpr t htemp
  have he : Function.update (Function.update t p (t q++t p)) q []=Function.update s p (s p).reverse := by
    funext i
    by_cases hi : i=p
    · subst i;simp [t,hpq,hpq.symm]
    · by_cases hj : i=q
      · subst i;simp [t,hpq,hpq.symm,hq]
      · simp [t,hi,hj]
  rw [he] at hh
  have h₂ : (moveOn q p r hpq.symm hqr hpr).Executes oracle t (Function.update s p (s p).reverse) (6*(s p).length+5) := by
    simpa [t] using hh
  convert seq_executes _ _ oracle h₁ h₂ using 1 <;> omega

theorem reverseInPlace_queryFree {k : ℕ} (p q r : Fin (k+1)) (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) :
    (reverseInPlace p q r hpq hpr hqr).QueryFree :=
  seq_queryFree _ _ (reverseOn_queryFree _ _ _) (moveOn_queryFree _ _ _ _ _ _)
end HiddenCircuits.Circuit.Runtime.SpectralTable
