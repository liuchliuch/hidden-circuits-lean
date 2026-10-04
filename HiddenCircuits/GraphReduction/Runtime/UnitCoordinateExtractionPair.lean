import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionState

/-! One actual coordinate-relaxation pair: two array reads, a matrix read,
physical bounded arithmetic, two array writes and complete scalar cleanup. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck UnitCoordinateExtraction

noncomputable def pairProgram : OracleBlock 22 := seq (readValue true) (seq (readValue false)
  (seq readEdge (seq arithmetic (seq (writeValue false) (seq (writeValue true)
    (seq (clear 7) (clear 8)))))))

def pairTime (n D B : ℕ) : ℕ := 2*lookupBound (n*(2*B+2)) n+110*(n+1)^2+
  102*(D+2*B+1)+2*DH.Runtime.WordArray.updateBound (n*(2*B+2)) n B+2*B+20

lemma scalar_pair {n : ℕ} (D : ℕ) (e : Bool) (u v : Fin n) (huv : u≠v) (x : Coordinates n) :
    Function.update (Function.update x v (UnitCoordinateExtractionScalar.right D (x u) (x v) e)) u
      (UnitCoordinateExtractionScalar.left D (x u) (x v) e) =pair D e u v x := by
  cases e
  · simp only [UnitCoordinateExtractionScalar.left,UnitCoordinateExtractionScalar.right,pair,Bool.false_eq_true,ite_false]
    funext i
    by_cases hi:i=u
    · subst i;simp [huv]
    · simp [hi]
  · rfl

lemma scalar_left_bound {n : ℕ} (D B : ℕ) (e : Bool) (u v : Fin n) (x : Coordinates n)
    (ho : ∀i,pair D e u v x i≤B) : UnitCoordinateExtractionScalar.left D (x u) (x v) e≤B := by
  have h := ho u
  cases e with
  | false => exact (pair_inflationary D false u v x u).trans h
  | true => simpa [pair,UnitCoordinateExtractionScalar.left] using h

lemma scalar_right_bound {n : ℕ} (D B : ℕ) (e : Bool) (u v : Fin n) (huv : u≠v) (x : Coordinates n)
    (ho : ∀i,pair D e u v x i≤B) : UnitCoordinateExtractionScalar.right D (x u) (x v) e≤B := by
  have h := ho v
  cases e <;> simpa [pair,UnitCoordinateExtractionScalar.right,Function.update_apply,huv.symm] using h

lemma pairProgram_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (f : Frame) (hn : f.n=n) (hp : f.payload=G.bits) (x : Coordinates n)
    (u v : Fin n) (huv : u≠v) (B : ℕ) (hx : ∀i,x i≤B)
    (ho : ∀i,pair f.D (G.edge u v) u v x i≤B) :
    ∃t,pairProgram.Executes g (state f (encoded x) u.val v.val [] [] [])
      (state f (encoded (pair f.D (G.edge u v) u v x)) u.val v.val [] [] []) t ∧
      t≤pairTime n f.D B := by
  let a := UnitCoordinateExtractionScalar.left f.D (x u) (x v) (G.edge u v)
  let b := UnitCoordinateExtractionScalar.right f.D (x u) (x v) (G.edge u v)
  have ha : a≤B := scalar_left_bound _ _ _ _ _ _ ho
  have hb : b≤B := scalar_right_bound _ _ _ _ _ huv _ ho
  let y := Function.update x v b
  have hy : ∀i,y i≤B := by intro i;by_cases hi:i=v <;> simp [y,Function.update_apply,hi,hb,hx]
  obtain ⟨c1,h1,b1⟩ := readFirst_executes g f x u v [] []
  obtain ⟨c2,h2,b2⟩ := readSecond_executes g f x u v (List.replicate (x u) true) []
  obtain ⟨c3,h3,b3⟩ := readEdge_executes g G f hn hp (encoded x) u v
    (List.replicate (x u) true) (List.replicate (x v) true)
  obtain ⟨c4,h4,b4⟩ := arithmetic_executes g f (encoded x) u.val v.val (x u) (x v) (G.edge u v)
  obtain ⟨c5,h5,b5⟩ := writeSecond_executes g f x u v (List.replicate a true) b []
  obtain ⟨c6,h6,b6⟩ := writeFirst_executes g f y u v a (List.replicate b true) []
  have he : Function.update y u a=pair f.D (G.edge u v) u v x := scalar_pair _ _ _ _ huv _
  rw [he] at h6
  have h7 : (clear (7 : Fin 23)).Executes g
      (state f (encoded (pair f.D (G.edge u v) u v x)) u.val v.val (List.replicate a true) (List.replicate b true) [])
      (state f (encoded (pair f.D (G.edge u v) u v x)) u.val v.val [] (List.replicate b true) []) (a+1) := by
    convert clear_executes g (7 : Fin 23) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state]
  have h8 : (clear (8 : Fin 23)).Executes g
      (state f (encoded (pair f.D (G.edge u v) u v x)) u.val v.val [] (List.replicate b true) [])
      (state f (encoded (pair f.D (G.edge u v) u v x)) u.val v.val [] [] []) (b+1) := by
    convert clear_executes g (8 : Fin 23) _ using 1
    · funext i;fin_cases i <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3
    (seq_executes _ _ g h4 (seq_executes _ _ g h5 (seq_executes _ _ g h6
      (seq_executes _ _ g h7 h8)))))),?_⟩
  have hL := encoded_length x B hx
  have hK := encoded_length y B hy
  have hun := u.isLt.le
  have hvn := v.isLt.le
  have b1' : c1≤lookupBound (n*(2*B+2)) n := b1.trans (by unfold lookupBound;gcongr <;> assumption)
  have b2' : c2≤lookupBound (n*(2*B+2)) n := b2.trans (by unfold lookupBound;gcongr <;> assumption)
  have b5' : c5≤DH.Runtime.WordArray.updateBound (n*(2*B+2)) n B := b5.trans (by
    unfold DH.Runtime.WordArray.updateBound;gcongr <;> assumption)
  have b6' : c6≤DH.Runtime.WordArray.updateBound (n*(2*B+2)) n B := b6.trans (by
    unfold DH.Runtime.WordArray.updateBound;gcongr <;> assumption)
  have hau := hx u
  have hbv := hx v
  unfold pairTime
  omega

lemma pairProgram_queryFree : pairProgram.QueryFree := seq_queryFree _ _ (readValue_queryFree _)
  (seq_queryFree _ _ (readValue_queryFree _) (seq_queryFree _ _ readEdge_queryFree
    (seq_queryFree _ _ arithmetic_queryFree (seq_queryFree _ _ (writeValue_queryFree _)
      (seq_queryFree _ _ (writeValue_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))))))
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
