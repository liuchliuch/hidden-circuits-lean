import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRootsLoop
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrellaProgram

/-! Ports and checked subroutine calls for all-root component recognition. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitOrderRoots
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

abbrev Best := UnitRecognitionRoots.Best
abbrev residual := @UnitRecognitionRoots.residual
abbrev good := @UnitRecognitionRoots.good
abbrev step := @UnitRecognitionRoots.step

def savedBits {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (b : Best n) : BitString :=
  (b.map (fun r => UnitRecognitionComponent.orderBits (UnitRecognitionComponent.component G A r).order)).getD []

lemma savedBits_length {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (b : Best n) :
    (savedBits G A b).length ≤ 2*(n+1)^2 := by
  cases b with
  | none => simp [savedBits]
  | some r => exact UnitRecognitionComponent.component_orderBits_length G A r

def state {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (b : Best n) (i : ℕ)
    (trial : Option (UnitRecognitionComponent.Data n)) (clock winner test eligible foundCopy decision : BitString) : Store 43 := fun r =>
  if h:r.val<37 then
    let s := UnitRecognitionComponent.store G A (trial.getD (UnitRecognitionComponent.emptyData A))
      [] winner [] [] [false] test eligible
    if trial.isNone && decide (r.val=3 ∨ r.val=4 ∨ r.val=33) then [] else s ⟨r.val,h⟩
  else if r.val=37 then liveBits (residual G A b) else if r.val=38 then [b.isSome]
  else if r.val=39 then List.replicate i true else if r.val=40 then clock
  else if r.val=41 then foundCopy else if r.val=42 then decision else savedBits G A b

def componentEmbedding : Fin 37 ↪ Fin 44 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun z : Fin 44 => z.val) h)
noncomputable def computeComponent : OracleBlock 43 := seq
  (copyOn 39 5 15 (by decide) (by decide) (by decide))
  (UnitRecognitionComponent.on componentEmbedding)

theorem computeComponent_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    ∃t, computeComponent.Executes g (state G A b i.val none clock [] [] [] [] [])
      (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] []) t ∧
      t≤2600*(n+1)^5 := by
  have h1 : (copyOn (39 : Fin 44) 5 15 (by decide) (by decide) (by decide)).Executes g
      (state G A b i.val none clock [] [] [] [] [])
      (state G A b i.val none clock (List.replicate i.val true) [] [] [] []) (5*i.val+2) := by
    convert copyOn_executes g (39 : Fin 44) 5 15 (by decide) (by decide) (by decide)
      (state G A b i.val none clock [] [] [] [] []) rfl using 1
    · funext j;fin_cases j <;> simp [state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState]
    · simp [state]
  obtain ⟨c,h2,b2⟩ := UnitRecognitionComponent.on_executes componentEmbedding g G A i
    (state G A b i.val none clock (List.replicate i.val true) [] [] [] [])
    (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] [])
    (by funext j;fin_cases j <;> rfl) (by funext j;fin_cases j <;> rfl)
    (by
      intro j hj
      have he : ¬j.val<37 := by intro h;exact hj ⟨j.val,h⟩ (Fin.ext rfl)
      simp [state,he])
  refine ⟨_,seq_executes _ _ g h1 h2,?_⟩
  have hi := i.isLt
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5)]

def umbrellaEmbedding : Fin 19 ↪ Fin 44 where
  toFun i := ![0,1,33,35,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20] i
  inj' := by decide +kernel
noncomputable def checkOrder : OracleBlock 43 := UnitRecognitionUmbrella.on umbrellaEmbedding

theorem checkOrder_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (b : Best n) (i : Fin n) (clock : BitString) :
    ∃t, checkOrder.Executes g
      (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] [])
      (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock []
        [UnitRecognitionUmbrella.check G (UnitRecognitionComponent.component G A i).order.reverse] [] [] []) t ∧
      t≤7200*(n+1)^5 := by
  obtain ⟨t,ht,hb⟩ := UnitRecognitionUmbrella.on_executes umbrellaEmbedding g G
    (UnitRecognitionComponent.component G A i).order.reverse
    (state G A b i.val (some (UnitRecognitionComponent.component G A i)) clock [] [] [] [] [])
    (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext j;fin_cases j <;> rfl
  · simp only [List.length_reverse] at hb
    have hl := UnitRecognitionComponent.component_order_length G A i
    have hm : ((UnitRecognitionComponent.component G A i).order.length+1)^3 ≤ (2*(n+1))^3 := by gcongr;omega
    have hx := Nat.mul_le_mul_left (900*(n+1)^2) hm
    nlinarith

def eligibleEmbedding : Fin 7 ↪ Fin 44 where
  toFun i := ![2,39,36,9,10,11,12] i
  inj' := by decide +kernel
noncomputable def readEligible : OracleBlock 43 := listLookupOn eligibleEmbedding

theorem readEligible_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (b : Best n) (i : Fin n) (s : UnitRecognitionComponent.Data n) (clock test : BitString) :
    ∃t, readEligible.Executes g (state G A b i.val (some s) clock [] test [] [] [])
      (state G A b i.val (some s) clock [] test [A[i.val]] [] []) t ∧ t≤100*(n+1)^2 := by
  obtain ⟨t,ht,hb⟩ := listLookupOn_executes eligibleEmbedding g
    (state G A b i.val (some s) clock [] test [] [] []) (liveWords A) i.val
    (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,?_⟩
  · convert ht using 1
    funext j;fin_cases j <;> simp [state,UnitRecognitionComponent.store,UnitRecognitionChoice.rawState,eligibleEmbedding,liveWords_get]
  · change t≤lookupBound (liveBits A).length i.val at hb
    rw [liveBits_length] at hb
    unfold lookupBound at hb
    have hi := i.isLt
    have hm := Nat.mul_le_mul_left n hi.le
    nlinarith

lemma computeComponent_queryFree : computeComponent.QueryFree := seq_queryFree _ _
  (copyOn_queryFree _ _ _ _ _ _) (UnitRecognitionComponent.on_queryFree _)
lemma checkOrder_queryFree : checkOrder.QueryFree := UnitRecognitionUmbrella.on_queryFree _
lemma readEligible_queryFree : readEligible.QueryFree := listLookupOn_queryFree _

end HiddenCircuits.GraphReduction.Runtime.UnitOrderRoots
