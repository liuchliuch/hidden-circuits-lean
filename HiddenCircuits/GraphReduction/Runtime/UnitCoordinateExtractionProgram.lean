import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionInitialize

/-! Fixed binary-stack coordinate extraction after the internally computed
umbrella permutation. All polynomial bounds are in the original vertex count. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck UnitCoordinateExtraction UnitIntervalOrder Polynomial

noncomputable def program : OracleBlock 22 := seq setup rounds

noncomputable def magnitudePolynomial : Polynomial ℕ := 2*(X+1)^2
noncomputable def arrayPolynomial : Polynomial ℕ := X*(2*magnitudePolynomial+2)
noncomputable def lookupPolynomial : Polynomial ℕ :=
  5*arrayPolynomial+5*X+(X+1)*(6*arrayPolynomial+14)+9
noncomputable def updatePolynomial : Polynomial ℕ :=
  X*(11*arrayPolynomial+20)+8*arrayPolynomial+5*X+15*magnitudePolynomial+42
noncomputable def pairPolynomial : Polynomial ℕ :=
  2*lookupPolynomial+110*(X+1)^2+102*((X+1)+2*magnitudePolynomial+1)+
    2*updatePolynomial+2*magnitudePolynomial+20
noncomputable def innerPolynomial : Polynomial ℕ := pairPolynomial+6*X+14
noncomputable def outerPolynomial : Polynomial ℕ := X*innerPolynomial+10*(X+1)*X+6*X+20
noncomputable def scanPolynomial : Polynomial ℕ := X*outerPolynomial+10*(X+1)*X+5
noncomputable def time : Polynomial ℕ := initializeTime+fuelPolynomial*(scanPolynomial+2)+3

lemma scanPolynomial_eval (n : ℕ) : scanPolynomial.eval n=scanTime n (n+1) (2*(n+1)^2) := by
  simp [scanPolynomial,outerPolynomial,innerPolynomial,pairPolynomial,lookupPolynomial,updatePolynomial,
    arrayPolynomial,magnitudePolynomial,scanTime,outerTime,innerTime,pairTime,lookupBound,DH.Runtime.WordArray.updateBound]
lemma scanTime_mono_D (n D E B : ℕ) (h : D≤E) : scanTime n D B≤scanTime n E B := by
  unfold scanTime outerTime innerTime pairTime
  gcongr

/-- Operational theorem with a purely mathematical invariant. The witness is
not supplied to the program; the following graph theorem derives it internally. -/
theorem program_executes_of_witness (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (ls : List (Fin n)) (hd : ls.Nodup) (hl : ls.length≤n) (z : Coordinates n)
    (hz : ∀p∈pairs ls,pair (max 1 n) (G.edge p.1 p.2) p.1 p.2 z=z)
    (hB : ∀i,z i≤2*(n+1)^2) :
    ∃t,program.Executes g (input n G.bits (labelBits ls))
      (state (readyFrame n G.bits (labelBits ls))
        (encoded (run (max 1 n) G.edge ls (fuel n) (fun _=>0))) 0 0 [] [] []) t ∧
      t≤time.eval n := by
  obtain ⟨c,hc,cb⟩ := initialize_executes g n G.bits (labelBits ls)
  obtain ⟨d,hd',db⟩ := rounds_execution g G (readyFrame n G.bits (labelBits ls)) rfl rfl
    (fun _=>0) z ls hd hl rfl rfl rfl (2*(n+1)^2) (fuel n) (fun _=>Nat.zero_le _) hz hB
  have he : {readyFrame n G.bits (labelBits ls) with clock:=[]}=readyFrame n G.bits (labelBits ls) := rfl
  rw [he] at hd'
  refine ⟨_,seq_executes _ _ g hc (whilePop_executes _ _ _ g hd'),?_⟩
  have hm := scanTime_mono_D n (max 1 n) (n+1) (2*(n+1)^2) (by omega)
  have hmul := Nat.mul_le_mul_left (fuel n) (Nat.add_le_add_right hm 2)
  dsimp only [readyFrame] at db
  simp only [time,eval_add,eval_mul,eval_ofNat,fuelPolynomial_eval,scanPolynomial_eval]
  omega

/-- Exact ordinary labeled-graph data to bounded natural coordinates, after
its own recognizer has supplied the order. No numerical witness or runtime
certificate is an input. -/
theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n)
    (ls : List (Fin n)) (hd : ls.Nodup) (hc : ∀v,v∈ls) (hu : ListUmbrella G.graph ls) :
    ∃t,program.Executes g (input n G.bits (labelBits ls))
      (state (readyFrame n G.bits (labelBits ls)) (encoded (coordinates G.graph ls)) 0 0 [] [] []) t ∧
      t≤time.eval n := by
  obtain ⟨z,hz,hb⟩ := list_grid_witness G.graph ls hd hc hu
  have hedge : (fun u v=>decide (G.graph.Adj u v))=G.edge := by
    funext u v;simp [MatrixGraph.graph]
  have hz' : ∀p∈pairs ls,pair (max 1 n) (G.edge p.1 p.2) p.1 p.2 z=z := by
    simpa [MatrixGraph.graph] using hz
  have hl : ls.length≤n := by simpa using hd.length_le_card
  have hB : ∀i,z i≤2*(n+1)^2 := by
    intro i
    have h := hb i
    have hm : max 1 n≤n+1 := by omega
    have hmul : 2*n*max 1 n≤2*(n+1)^2 := by
      calc 2*n*max 1 n ≤ 2*(n+1)*(n+1) := by gcongr <;> omega
           _ = _ := by ring
    omega
  have h := program_executes_of_witness g (MatrixData.ofGraph G) ls hd hl z hz' hB
  simpa only [coordinates,hedge,MatrixData.ofGraph] using h

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ initialize_queryFree rounds_queryFree

noncomputable def on {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) (g : BitString → ℕ)
    {n : ℕ} (G : MatrixGraph n) (ls : List (Fin n)) (hd : ls.Nodup) (hc : ∀v,v∈ls)
    (hu : ListUmbrella G.graph ls) (s t : Store k)
    (hs : s∘φ=input n G.bits (labelBits ls))
    (ht : t∘φ=state (readyFrame n G.bits (labelBits ls)) (encoded (coordinates G.graph ls)) 0 0 [] [] [])
    (hf : ∀i,(∀j,φ j≠i)→t i=s i) :
    ∃c,(on φ).Executes g s t c ∧c≤time.eval n := by
  obtain ⟨c,hc',hb⟩ := program_executes g G ls hd hc hu
  exact ⟨c,rename_executes_to _ φ g hc' hs ht hf,hb⟩
lemma on_queryFree {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionMachine
