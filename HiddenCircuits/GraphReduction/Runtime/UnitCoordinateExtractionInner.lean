import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionPair
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrellaInner

/-! Physical inner tail scan of the original-label order. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck UnitCoordinateExtraction

abbrev labelBits {n : ℕ} (ls : List (Fin n)) := UnitRecognitionUmbrella.encoded ls

def parseEmbedding (first : Bool) : Fin 4 ↪ Fin 23 where
  toFun i := ![if first then 10 else 11,if first then 5 else 6,18,22] i
  inj' := by cases first <;> decide +kernel
noncomputable def parseLabel (first : Bool) : OracleBlock 22 := UnitRecognitionLabelRead.on (parseEmbedding first)
noncomputable def innerBody : OracleBlock 22 := seq (parseLabel false) (seq pairProgram (clear 6))
noncomputable def innerLoop : OracleBlock 22 := whilePop 11 innerBody innerBody

def innerTime (n D B : ℕ) := pairTime n D B+6*n+14

lemma innerBody_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (f : Frame) (hn : f.n=n) (hp : f.payload=G.bits) (x z : Coordinates n)
    (u v : Fin n) (huv : u≠v) (vs : List (Fin n)) (B : ℕ) (hx : x≤z)
    (hz : pair f.D (G.edge u v) u v z=z) (hB : ∀i,z i≤B) :
    ∃t,innerBody.Executes g
      (state {f with inner:=pairBits (List.replicate v.val true) (labelBits vs)} (encoded x) u.val 0 [] [] [])
      (state {f with inner:=labelBits vs} (encoded (pair f.D (G.edge u v) u v x)) u.val 0 [] [] []) t ∧
      t+2 ≤ innerTime n f.D B := by
  have h1 : (parseLabel false).Executes g
      (state {f with inner:=pairBits (List.replicate v.val true) (labelBits vs)} (encoded x) u.val 0 [] [] [])
      (state {f with inner:=labelBits vs} (encoded x) u.val v.val [] [] []) (5*v.val+7) := by
    convert UnitRecognitionLabelRead.on_executes (parseEmbedding false) g
      (state {f with inner:=pairBits (List.replicate v.val true) (labelBits vs)} (encoded x) u.val 0 [] [] [])
      (state {f with inner:=labelBits vs} (encoded x) u.val v.val [] [] [])
      (List.replicate v.val true) (labelBits vs)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  have hOut : pair f.D (G.edge u v) u v x≤z := by
    calc pair f.D (G.edge u v) u v x ≤ pair f.D (G.edge u v) u v z := pair_monotone _ _ _ _ hx
         _ = z := hz
  obtain ⟨c2,h2,b2⟩ := pairProgram_executes g G {f with inner:=labelBits vs} hn hp x u v huv B
    (fun i=>(hx i).trans (hB i)) (fun i=>(hOut i).trans (hB i))
  have h3 : (clear (6 : Fin 23)).Executes g
      (state {f with inner:=labelBits vs} (encoded (pair f.D (G.edge u v) u v x)) u.val v.val [] [] [])
      (state {f with inner:=labelBits vs} (encoded (pair f.D (G.edge u v) u v x)) u.val 0 [] [] []) (v.val+1) := by
    convert clear_executes g (6 : Fin 23) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hv := v.isLt
  dsimp only at b2
  unfold innerTime
  omega

lemma innerLoop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (f : Frame) (hn : f.n=n) (hp : f.payload=G.bits) (x z : Coordinates n)
    (u : Fin n) (vs : List (Fin n)) (hne : ∀v∈vs,u≠v) (B : ℕ) (hx : x≤z)
    (hz : ∀v∈vs,pair f.D (G.edge u v) u v z=z) (hB : ∀i,z i≤B) :
    ∃t,WhileExecution (11 : Fin 23) innerBody innerBody g
      (state {f with inner:=labelBits vs} (encoded x) u.val 0 [] [] [])
      (state {f with inner:=[]} (encoded (inner f.D G.edge u vs x)) u.val 0 [] [] []) t ∧
      t≤vs.length*innerTime n f.D B+1 := by
  induction vs generalizing x with
  | nil =>
    exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | cons v vs ih =>
    have hv := hne v (by simp)
    have hzv := hz v (by simp)
    obtain ⟨c,hc,cb⟩ := innerBody_executes g G f hn hp x z u v hv vs B hx hzv hB
    have hOut : pair f.D (G.edge u v) u v x≤z := by
      calc pair f.D (G.edge u v) u v x ≤ pair f.D (G.edge u v) u v z := pair_monotone _ _ _ _ hx
           _ = z := hzv
    obtain ⟨t,ht,tb⟩ := ih (pair f.D (G.edge u v) u v x)
      (fun w hw=>hne w (by simp [hw])) hOut (fun w hw=>hz w (by simp [hw]))
    have he : Function.update (state {f with inner:=labelBits (v::vs)} (encoded x) u.val 0 [] [] [])
        (11 : Fin 23) (pairBits (List.replicate v.val true) (labelBits vs)) =
        state {f with inner:=pairBits (List.replicate v.val true) (labelBits vs)} (encoded x) u.val 0 [] [] [] := by
      funext i;fin_cases i <;> rfl
    refine ⟨1+c+1+t,?_,?_⟩
    · apply WhileExecution.one (show state {f with inner:=labelBits (v::vs)} (encoded x) u.val 0 [] [] [] 11=
        true::pairBits (List.replicate v.val true) (labelBits vs) from rfl)
      · rw [he];exact hc
      · exact ht
    · simp only [List.length_cons];nlinarith

lemma parseLabel_queryFree (first : Bool) : (parseLabel first).QueryFree := UnitRecognitionLabelRead.on_queryFree _
lemma innerBody_queryFree : innerBody.QueryFree := seq_queryFree _ _ (parseLabel_queryFree _)
  (seq_queryFree _ _ pairProgram_queryFree (clear_queryFree _))
lemma innerLoop_queryFree : innerLoop.QueryFree := whilePop_queryFree _ _ _ innerBody_queryFree innerBody_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
