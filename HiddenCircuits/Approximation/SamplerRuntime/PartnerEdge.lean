import HiddenCircuits.Approximation.SamplerRuntime.PartnerConjugation
import HiddenCircuits.Complexity.GraphVerifier.MatrixLookup
import HiddenCircuits.Complexity.GraphEncoding
import HiddenCircuits.Approximation.Quasimonotone.PartnerSwitch

/-! Real partner-edge lookup and the exact two-edge conjugation acceptance criterion. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerEdge
open Complexity Complexity.OracleBlock GraphVerifier.Runtime DH.Runtime QuasimonotoneProof.PartnerSwitch
variable {n : ℕ}
abbrev unary (n : ℕ) : BitString := List.replicate n true

def state (n : ℕ) (graph data : BitString) (v : ℕ) (out partner : BitString) : Store 10 := fun r =>
  if r.val=0 then unary n else if r.val=1 then graph else if r.val=2 then data else if r.val=3 then unary v
  else if r.val=4 then out else if r.val=5 then partner else []
def readMap : Fin 8 ↪ Fin 11 where
  toFun i := ![2,3,5,6,7,8,9,10] i
  inj' := by decide +kernel
def matrixMap : Fin 9 ↪ Fin 11 where
  toFun i := ![0,3,5,1,4,6,7,8,9] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 10 := seq (WordArray.readOn readMap)
  (seq (matrixLookupOn matrixMap) (clear 5))

lemma matrix_bit (G : MatrixGraph n) (i j : Fin n) : G.bits[j.val+n*i.val]?.toList=[G.edge i j] := by
  have he : (finProdFinEquiv (i,j)).val=j.val+n*i.val := by rfl
  have hi : j.val+n*i.val<G.bits.length := by rw [←he,G.bits_length];exact (finProdFinEquiv (i,j)).isLt
  rw [List.getElem?_eq_getElem hi]
  change [G.bits[j.val+n*i.val]]=[G.edge i j]
  congr 1
  have hh := G.get_bits i j (by rw [G.bits_length];exact (finProdFinEquiv (i,j)).isLt)
  simpa only [he,List.get_eq_getElem] using hh

theorem program_executes (g : BitString → ℕ) (G : MatrixGraph n) (π : Equiv.Perm (Fin n)) (v : Fin n) :
    ∃t,program.Executes g (state n G.bits (Output.witness π) v.val [] [])
      (state n G.bits (Output.witness π) v.val [G.edge v (π v)] []) t ∧ t≤10000*(n+1)^4 := by
  obtain ⟨a,ha,hba⟩ := WordArray.readOn_executes readMap g (state n G.bits (Output.witness π) v.val [] [])
    (Switch.rowWords π) v.val (by funext r;fin_cases r <;> rfl)
  rw [Switch.rowWords_get] at ha
  have ea : Function.update (state n G.bits (Output.witness π) v.val [] []) (readMap 2) (unary (π v).val)=
      state n G.bits (Output.witness π) v.val [] (unary (π v).val) := by funext r;fin_cases r <;> rfl
  rw [ea] at ha
  have hb := matrixLookupOn_executes matrixMap g (state n G.bits (Output.witness π) v.val [] (unary (π v).val))
    n v.val (π v).val G.bits (by funext r;fin_cases r <;> rfl)
  rw [matrix_bit] at hb
  have eb : Function.update (state n G.bits (Output.witness π) v.val [] (unary (π v).val)) (matrixMap 4) [G.edge v (π v)]=
      state n G.bits (Output.witness π) v.val [G.edge v (π v)] (unary (π v).val) := by funext r;fin_cases r <;> rfl
  rw [eb] at hb
  have hc : (clear (5:Fin 11)).Executes g (state n G.bits (Output.witness π) v.val [G.edge v (π v)] (unary (π v).val))
      (state n G.bits (Output.witness π) v.val [G.edge v (π v)] []) ((π v).val+1) := by
    convert clear_executes g (5:Fin 11) _ using 1
    · funext r;fin_cases r <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  have hm := matrixLookupCost_in_range n v.val (π v).val G.bits v.isLt (π v).isLt
  have hl := Switch.rows_encoded_length (fun i => (π i).val) (fun i => (π i).isLt.le)
  change (encodeBitList (Switch.rowWords π)).length≤2*n*n+2*n at hl
  have hv := v.isLt
  have hp := (π v).isLt
  have hmul := Nat.mul_le_mul_left v.val hl
  have hmul' := Nat.mul_le_mul_right (2*n*n+2*n) hv.le
  unfold GraphReduction.Runtime.lookupBound at hba
  nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (WordArray.readOn_queryFree _)
  (seq_queryFree _ _ (matrixLookupOn_queryFree _) (clear_queryFree _))

/-- Conjugation can change a non-proposed row only to a proposed vertex. Its
involutivity then supplies that edge from one of the two checked reverse edges. -/
theorem conjugate_valid_iff (G : MatrixGraph n) (P : PerfectPartner G.graph) (a b : Fin n) :
    (∀x,G.graph.Adj x (conjugate a b P.val x)) ↔
      G.graph.Adj a (conjugate a b P.val a) ∧ G.graph.Adj b (conjugate a b P.val b) := by
  constructor
  · intro h;exact ⟨h a,h b⟩
  · rintro ⟨ha,hb⟩ x
    have hinv := conjugate_partner_involutive a b P.val P.property.1
    by_cases hxa : x=a
    · simpa [hxa] using ha
    · by_cases hxb : x=b
      · simpa [hxb] using hb
      · by_cases hpa : P.val x=a
        · have hc : conjugate a b P.val x=b := by simp [conjugate,Equiv.swap_apply_of_ne_of_ne hxa hxb,hpa]
          have hi : conjugate a b P.val b=x := by simpa only [hc] using hinv x
          rw [hi] at hb
          rw [hc]
          exact G.graph.adj_symm hb
        · by_cases hpb : P.val x=b
          · have hc : conjugate a b P.val x=a := by simp [conjugate,Equiv.swap_apply_of_ne_of_ne hxa hxb,hpb]
            have hi : conjugate a b P.val a=x := by simpa only [hc] using hinv x
            rw [hi] at ha
            rw [hc]
            exact G.graph.adj_symm ha
          · simpa [conjugate,Equiv.swap_apply_of_ne_of_ne hxa hxb,Equiv.swap_apply_of_ne_of_ne hpa hpb] using P.property.2 x

end HiddenCircuits.Approximation.SamplerRuntime.PartnerEdge
