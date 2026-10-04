import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrellaCell
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionLabelRead

/-! The innermost tail scan consumes canonical original-vertex words. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

def inner {n : ℕ} (G : MatrixData n) (u v : Fin n) (ls : List (Fin n)) : Bool := ls.all (cell G u v)
def middle {n : ℕ} (G : MatrixData n) (u : Fin n) : List (Fin n) → Bool
  | [] => true
  | v::vs => inner G u v vs && middle G u vs
def check {n : ℕ} (G : MatrixData n) : List (Fin n) → Bool
  | [] => true
  | u::us => middle G u us && check G us

lemma encoded_cons {n : ℕ} (v : Fin n) (vs : List (Fin n)) :
    encoded (v::vs)=true::pairBits (List.replicate v.val true) (encoded vs) := rfl
lemma encoded_nil {n : ℕ} : encoded ([] : List (Fin n))=[] := rfl
lemma encoded_length_le {n : ℕ} (ls : List (Fin n)) : (encoded ls).length≤2*(n+1)*ls.length := by
  induction ls with
  | nil => simp [encoded,words,encodeBitList]
  | cons v vs ih =>
    have hv := v.isLt
    rw [encoded_cons]
    simp only [List.length_cons,pairBits_length,List.length_replicate]
    nlinarith

def parseEmbedding (which : Fin 3) : Fin 4 ↪ Fin 19 where
  toFun i := if which.val=0 then ![4,7,14,18] i else if which.val=1 then ![5,8,14,18] i else ![6,9,14,18] i
  inj' := by fin_cases which <;> decide +kernel
noncomputable def parseLabel (which : Fin 3) : OracleBlock 18 := UnitRecognitionLabelRead.on (parseEmbedding which)
noncomputable def innerBody : OracleBlock 18 := seq (parseLabel 2) (seq cellProgram (clear 9))
noncomputable def innerLoop : OracleBlock 18 := whilePop 6 innerBody innerBody

theorem innerBody_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (u v w : Fin n) (original outer mid : BitString) (rest : List (Fin n)) (acc : Bool) :
    ∃t, innerBody.Executes g
      (state n u.val v.val 0 G.bits original outer mid (pairBits (List.replicate w.val true) (encoded rest)) [acc] [] [] [] [] [])
      (state n u.val v.val 0 G.bits original outer mid (encoded rest) [acc && cell G u v w] [] [] [] [] []) t ∧
      t≤400*(n+1)^2 := by
  have h1 : (parseLabel 2).Executes g
      (state n u.val v.val 0 G.bits original outer mid (pairBits (List.replicate w.val true) (encoded rest)) [acc] [] [] [] [] [])
      (state n u.val v.val w.val G.bits original outer mid (encoded rest) [acc] [] [] [] [] []) (5*w.val+7) := by
    convert UnitRecognitionLabelRead.on_executes (parseEmbedding 2) g
      (state n u.val v.val 0 G.bits original outer mid (pairBits (List.replicate w.val true) (encoded rest)) [acc] [] [] [] [] [])
      (state n u.val v.val w.val G.bits original outer mid (encoded rest) [acc] [] [] [] [] [])
      (List.replicate w.val true) (encoded rest)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  obtain ⟨c,h2,b2⟩ := cellProgram_executes g G u v w original outer mid (encoded rest) acc
  have h3 : (clear (9 : Fin 19)).Executes g
      (state n u.val v.val w.val G.bits original outer mid (encoded rest) [acc && cell G u v w] [] [] [] [] [])
      (state n u.val v.val 0 G.bits original outer mid (encoded rest) [acc && cell G u v w] [] [] [] [] []) (w.val+1) := by
    convert clear_executes g (9 : Fin 19) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hw := w.isLt
  nlinarith

theorem innerLoop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (u v : Fin n) (original outer mid : BitString) (ls : List (Fin n)) (acc : Bool) :
    ∃t, WhileExecution (6 : Fin 19) innerBody innerBody g
      (state n u.val v.val 0 G.bits original outer mid (encoded ls) [acc] [] [] [] [] [])
      (state n u.val v.val 0 G.bits original outer mid [] [acc && inner G u v ls] [] [] [] [] []) t ∧
      t≤ls.length*(400*(n+1)^2+2)+1 := by
  induction ls generalizing acc with
  | nil =>
    refine ⟨1,?_,by simp⟩
    simpa only [inner,List.all_nil,Bool.and_true,encoded_nil] using (WhileExecution.empty
      (stack := (6 : Fin 19)) (B := innerBody) (C := innerBody) (g := g)
      (state n u.val v.val 0 G.bits original outer mid [] [acc] [] [] [] [] []) rfl)
  | cons w ws ih =>
    obtain ⟨c,hc,hcb⟩ := innerBody_executes g G u v w original outer mid ws acc
    obtain ⟨t,ht,htb⟩ := ih (acc && cell G u v w)
    have he : Function.update
        (state n u.val v.val 0 G.bits original outer mid (encoded (w::ws)) [acc] [] [] [] [] []) 6
        (pairBits (List.replicate w.val true) (encoded ws)) =
        state n u.val v.val 0 G.bits original outer mid (pairBits (List.replicate w.val true) (encoded ws)) [acc] [] [] [] [] [] := by
      funext i;fin_cases i <;> rfl
    have h := WhileExecution.one (show state n u.val v.val 0 G.bits original outer mid
      (encoded (w::ws)) [acc] [] [] [] [] [] 6=true::pairBits (List.replicate w.val true) (encoded ws) from rfl)
      (by rw [he];exact hc) ht
    refine ⟨1+c+1+t,?_,?_⟩
    · simpa only [inner,List.all_cons,Bool.and_assoc] using h
    · simp only [List.length_cons];nlinarith

lemma innerBody_queryFree : innerBody.QueryFree := seq_queryFree _ _ (UnitRecognitionLabelRead.on_queryFree _)
  (seq_queryFree _ _ cellProgram_queryFree (clear_queryFree _))
lemma innerLoop_queryFree : innerLoop.QueryFree := whilePop_queryFree _ _ _ innerBody_queryFree innerBody_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrella
