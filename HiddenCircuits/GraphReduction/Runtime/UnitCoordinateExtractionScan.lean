import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionInner

/-! Literal complete pair scans. Both label tails are physically copied,
parsed and consumed; the immutable original-label array remains available. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck UnitCoordinateExtraction

noncomputable def outerBody : OracleBlock 22 := seq (parseLabel true)
  (seq (copyOn 10 11 17 (by decide) (by decide) (by decide)) (seq innerLoop (clear 5)))
noncomputable def outerLoop : OracleBlock 22 := whilePop 10 outerBody outerBody
noncomputable def scanProgram : OracleBlock 22 := seq
  (copyOn 2 10 17 (by decide) (by decide) (by decide)) outerLoop

def outerTime (n D B m : ℕ) := m*innerTime n D B+10*(n+1)*m+6*n+20
def scanTime (n D B : ℕ) := n*outerTime n D B n+10*(n+1)*n+5

lemma outerBody_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (f : Frame) (hn : f.n=n) (hp : f.payload=G.bits) (x z : Coordinates n)
    (u : Fin n) (us : List (Fin n)) (hne : ∀v∈us,u≠v) (B m : ℕ) (hl : us.length≤m)
    (hx : x≤z) (hz : ∀v∈us,pair f.D (G.edge u v) u v z=z) (hB : ∀i,z i≤B) :
    ∃t,outerBody.Executes g
      (state {f with outer:=pairBits (List.replicate u.val true) (labelBits us),inner:=[]} (encoded x) 0 0 [] [] [])
      (state {f with outer:=labelBits us,inner:=[]} (encoded (inner f.D G.edge u us x)) 0 0 [] [] []) t ∧
      t+2 ≤ outerTime n f.D B m := by
  have h1 : (parseLabel true).Executes g
      (state {f with outer:=pairBits (List.replicate u.val true) (labelBits us),inner:=[]} (encoded x) 0 0 [] [] [])
      (state {f with outer:=labelBits us,inner:=[]} (encoded x) u.val 0 [] [] []) (5*u.val+7) := by
    convert UnitRecognitionLabelRead.on_executes (parseEmbedding true) g
      (state {f with outer:=pairBits (List.replicate u.val true) (labelBits us),inner:=[]} (encoded x) 0 0 [] [] [])
      (state {f with outer:=labelBits us,inner:=[]} (encoded x) u.val 0 [] [] [])
      (List.replicate u.val true) (labelBits us)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp
  have h2 : (copyOn (10 : Fin 23) 11 17 (by decide) (by decide) (by decide)).Executes g
      (state {f with outer:=labelBits us,inner:=[]} (encoded x) u.val 0 [] [] [])
      (state {f with outer:=labelBits us,inner:=labelBits us} (encoded x) u.val 0 [] [] [])
      (5*(labelBits us).length+2) := by
    convert copyOn_executes g (10 : Fin 23) 11 17 (by decide) (by decide) (by decide)
      (state {f with outer:=labelBits us,inner:=[]} (encoded x) u.val 0 [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  obtain ⟨c3,h3,b3⟩ := innerLoop_execution g G {f with outer:=labelBits us} hn hp x z u us hne B hx hz hB
  have h4 : (clear (5 : Fin 23)).Executes g
      (state {f with outer:=labelBits us,inner:=[]} (encoded (inner f.D G.edge u us x)) u.val 0 [] [] [])
      (state {f with outer:=labelBits us,inner:=[]} (encoded (inner f.D G.edge u us x)) 0 0 [] [] []) (u.val+1) := by
    convert clear_executes g (5 : Fin 23) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2
    (seq_executes _ _ g (whilePop_executes _ _ _ g h3) h4)),?_⟩
  dsimp only at b3
  have hu := u.isLt
  have hE : (labelBits us).length≤2*(n+1)*us.length := UnitRecognitionUmbrella.encoded_length_le us
  have hI := Nat.mul_le_mul_right (innerTime n f.D B) hl
  have hL := Nat.mul_le_mul_left (2*(n+1)) hl
  unfold outerTime
  nlinarith

lemma outerLoop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (f : Frame) (hn : f.n=n) (hp : f.payload=G.bits) (x z : Coordinates n)
    (ls : List (Fin n)) (hd : ls.Nodup) (B m : ℕ) (hl : ls.length≤m)
    (hx : x≤z) (hz : ∀p∈pairs ls,pair f.D (G.edge p.1 p.2) p.1 p.2 z=z) (hB : ∀i,z i≤B) :
    ∃t,WhileExecution (10 : Fin 23) outerBody outerBody g
      (state {f with outer:=labelBits ls,inner:=[]} (encoded x) 0 0 [] [] [])
      (state {f with outer:=[],inner:=[]} (encoded (scan f.D G.edge ls x)) 0 0 [] [] []) t ∧
      t≤ls.length*outerTime n f.D B m+1 := by
  induction ls generalizing x with
  | nil => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | cons u us ih =>
    have hd' := List.nodup_cons.mp hd
    have hne : ∀v∈us,u≠v := by intro v hv he;subst v;exact hd'.1 hv
    have hz' : ∀v∈us,pair f.D (G.edge u v) u v z=z := by
      intro v hv;exact hz (u,v) (by simp [pairs,hv])
    obtain ⟨c,hc,cb⟩ := outerBody_executes g G f hn hp x z u us hne B m (by simp only [List.length_cons] at hl;omega) hx hz' hB
    have hOut := inner_le_witness f.D G.edge u us x z hx hz'
    obtain ⟨t,ht,tb⟩ := ih (inner f.D G.edge u us x) hd'.2 (by simp only [List.length_cons] at hl;omega)
      hOut (fun p hp=>hz p (by simp [pairs,hp]))
    have he : Function.update
        (state {f with outer:=labelBits (u::us),inner:=[]} (encoded x) 0 0 [] [] []) (10 : Fin 23)
        (pairBits (List.replicate u.val true) (labelBits us)) =
        state {f with outer:=pairBits (List.replicate u.val true) (labelBits us),inner:=[]} (encoded x) 0 0 [] [] [] := by
      funext i;fin_cases i <;> rfl
    refine ⟨1+c+1+t,?_,?_⟩
    · apply WhileExecution.one (show state {f with outer:=labelBits (u::us),inner:=[]} (encoded x) 0 0 [] [] [] 10=
        true::pairBits (List.replicate u.val true) (labelBits us) from rfl)
      · rw [he];exact hc
      · exact ht
    · simp only [List.length_cons];nlinarith

lemma scanProgram_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (f : Frame) (hn : f.n=n) (hp : f.payload=G.bits) (x z : Coordinates n)
    (ls : List (Fin n)) (hd : ls.Nodup) (hl : ls.length≤n) (hf : f.order=labelBits ls)
    (he : f.outer=[]) (hi : f.inner=[]) (B : ℕ) (hx : x≤z)
    (hz : ∀p∈pairs ls,pair f.D (G.edge p.1 p.2) p.1 p.2 z=z) (hB : ∀i,z i≤B) :
    ∃t,scanProgram.Executes g (state f (encoded x) 0 0 [] [] [])
      (state f (encoded (scan f.D G.edge ls x)) 0 0 [] [] []) t ∧ t≤scanTime n f.D B := by
  have h1 : (copyOn (2 : Fin 23) 10 17 (by decide) (by decide) (by decide)).Executes g
      (state f (encoded x) 0 0 [] [] [])
      (state {f with outer:=labelBits ls,inner:=[]} (encoded x) 0 0 [] [] []) (5*(labelBits ls).length+2) := by
    convert copyOn_executes g (2 : Fin 23) 10 17 (by decide) (by decide) (by decide) (state f (encoded x) 0 0 [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state,hf,he,hi]
    · simp [state,hf]
  obtain ⟨c,hc,cb⟩ := outerLoop_execution g G f hn hp x z ls hd B n hl hx hz hB
  have hframe : {f with outer:=[],inner:=[]}=f := by cases f;simp_all
  rw [hframe] at hc
  refine ⟨_,seq_executes _ _ g h1 (whilePop_executes _ _ _ g hc),?_⟩
  have hE : (labelBits ls).length≤2*(n+1)*ls.length := UnitRecognitionUmbrella.encoded_length_le ls
  have hI := Nat.mul_le_mul_right (outerTime n f.D B n) hl
  have hL := Nat.mul_le_mul_left (2*(n+1)) hl
  unfold scanTime
  nlinarith

lemma outerBody_queryFree : outerBody.QueryFree := seq_queryFree _ _ (parseLabel_queryFree _)
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ innerLoop_queryFree (clear_queryFree _)))
lemma outerLoop_queryFree : outerLoop.QueryFree := whilePop_queryFree _ _ _ outerBody_queryFree outerBody_queryFree
lemma scanProgram_queryFree : scanProgram.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) outerLoop_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
