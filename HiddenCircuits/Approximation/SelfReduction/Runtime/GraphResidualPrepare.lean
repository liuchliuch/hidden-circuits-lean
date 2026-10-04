import HiddenCircuits.Approximation.Initialization.ResidualGraphFrame
import HiddenCircuits.Approximation.Initialization.MaskPair
import HiddenCircuits.Complexity.GraphVerifier.TwoParse
import HiddenCircuits.Complexity.OracleMove

/-! Raw canonical ordinary-graph decoding and actual retained-mask construction.
Only graph bytes and a unary chosen partner are provided to the finite program. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidual
open Complexity OracleBlock GraphVerifier GraphVerifier.Runtime Initialization

abbrev unary (n : ℕ) : BitString := List.replicate n true

def retained {N : ℕ} (j : Fin (N+1)) : Finset (Fin (N+1)) :=
  (Finset.univ.erase 0).erase j

def state (raw chosen : BitString) (N : ℕ) (payload mask flag : BitString) : Store 18 := fun r =>
  if r.val=0 then raw else if r.val=1 then chosen else if r.val=2 then unary N
  else if r.val=3 then payload else if r.val=4 then mask else if r.val=6 then flag else []

/-- Raw input/output on zero, preserved chosen partner on one, all scratch empty. -/
def inputStore (raw chosen : BitString) : Store 18 := state raw chosen 0 [] [] []

def parsePorts : Fin 4 ↪ Fin 19 where
  toFun i := ![0,2,5,6] i
  inj' := by decide +kernel

def maskPorts : Fin 7 ↪ Fin 19 where
  toFun i := ![2,5,1,4,6,7,8] i
  inj' := by decide +kernel

noncomputable def unpack : OracleBlock 18 := seq (unpairOn parsePorts)
  (seq (clear 6) (moveOn 0 3 5 (by decide) (by decide) (by decide)))
noncomputable def makeMask : OracleBlock 18 := MaskPair.on maskPorts
noncomputable def prepare : OracleBlock 18 := seq unpack makeMask

lemma unpack_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (chosen : BitString) :
    ∃ t,unpack.Executes g (inputStore (GraphInput.encode ⟨N,G⟩) chosen)
      (state [] chosen N G.bits [] []) t ∧ t≤9*N*N+6*N+20 := by
  have h1 : (unpairOn parsePorts).Executes g (inputStore (GraphInput.encode ⟨N,G⟩) chosen)
      (state G.bits chosen N [] [] [true]) (parseCost (GraphInput.encode ⟨N,G⟩)+2*N+1) := by
    have he := unpairOn_executes parsePorts g (inputStore (GraphInput.encode ⟨N,G⟩) chosen)
      (state G.bits chosen N [] [] [true]) (GraphInput.encode ⟨N,G⟩)
    simp only [GraphInput.encode,parse_pair,List.length_replicate] at he ⊢
    apply he
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr
      fin_cases r
      all_goals first | rfl | exact (hr 0 rfl).elim | exact (hr 1 rfl).elim | exact (hr 3 rfl).elim
  have h2 : (clear (6:Fin 19)).Executes g (state G.bits chosen N [] [] [true])
      (state G.bits chosen N [] [] []) 2 := by
    convert clear_executes g (6:Fin 19) (state G.bits chosen N [] [] [true]) using 1
    funext r;fin_cases r <;> rfl
  have h3 : (moveOn (0:Fin 19) 3 5 (by decide) (by decide) (by decide)).Executes g
      (state G.bits chosen N [] [] []) (state [] chosen N G.bits [] []) (6*(N*N)+5) := by
    convert moveOn_executes g (0:Fin 19) 3 5 (by decide) (by decide) (by decide)
      (state G.bits chosen N [] [] []) rfl using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 h3),?_⟩
  have hb := unpair_cost_bound (GraphInput.encode ⟨N,G⟩)
  simp only [GraphInput.encode,parse_pair,List.length_replicate,pairBits_length,MatrixGraph.bits_length] at hb
  change parseCost (GraphInput.encode ⟨N,G⟩)+2*N+1≤_ at hb
  nlinarith

lemma mask_univ (N : ℕ) : MaskEnumerationSemantics.mask (Finset.univ : Finset (Fin N))=unary N := by
  simp [MaskEnumerationSemantics.mask]

lemma makeMask_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    ∃ t,makeMask.Executes g (state [] (unary j.val) (N+1) G.bits [] [])
      (state [] (unary j.val) (N+1) G.bits (MaskEnumerationSemantics.mask (retained j)) []) t ∧
      t≤29*(N+1)+32 := by
  obtain ⟨t,ht,hb⟩ := MaskPair.on_executes maskPorts g
    (state [] (unary j.val) (N+1) G.bits [] []) Finset.univ (0:Fin (N+1)) j
    (by rw [mask_univ];funext r;fin_cases r <;> simp [state,maskPorts,MaskPair.state])
  refine ⟨t,?_,hb⟩
  convert ht using 1
  funext r;fin_cases r <;> simp [state,maskPorts,retained]

lemma prepare_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph (N+1)) (j : Fin (N+1)) :
    ∃ t,prepare.Executes g (inputStore (GraphInput.encode ⟨N+1,G⟩) (unary j.val))
      (state [] (unary j.val) (N+1) G.bits (MaskEnumerationSemantics.mask (retained j)) []) t ∧
      t≤9*(N+1)*(N+1)+35*(N+1)+54 := by
  obtain ⟨a,ha,hab⟩ := unpack_executes g G (unary j.val)
  obtain ⟨b,hb,hbb⟩ := makeMask_executes g G j
  exact ⟨_,seq_executes _ _ g ha hb,by omega⟩

lemma prepare_queryFree : prepare.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (unpairOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _)))
  (MaskPair.on_queryFree _)

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidual
