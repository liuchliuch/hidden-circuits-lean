import HiddenCircuits.Approximation.SamplerRuntime.Output
import HiddenCircuits.Approximation.SamplerRuntime.RuntimeBounds

/-! Read both original partners, then execute two physical row-array swaps.
The saved partner words remain available for a charged rejection undo. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerConjugation
open Complexity Complexity.OracleBlock DH.Runtime Approximation
variable {n : ℕ}
abbrev unary (n : ℕ) : BitString := List.replicate n true

def candidate (π : Equiv.Perm (Fin n)) (a b : Fin n) : Equiv.Perm (Fin n) :=
  MonotoneEndpoints.transpose (MonotoneEndpoints.transpose π (π a) (π b)) a b

def state (data : BitString) (a b : ℕ) (left right : BitString) : Store 11 := fun r =>
  if r.val=0 then data else if r.val=1 then unary a else if r.val=2 then unary b
  else if r.val=3 then left else if r.val=4 then right else []
def leftRead : Fin 8 ↪ Fin 12 where
  toFun i := ![0,1,3,5,6,7,8,9] i
  inj' := by decide +kernel
def rightRead : Fin 8 ↪ Fin 12 where
  toFun i := ![0,2,4,5,6,7,8,9] i
  inj' := by decide +kernel
def partnerMap : Fin 10 ↪ Fin 12 where
  toFun i := ![0,3,4,5,6,7,8,9,10,11] i
  inj' := by decide +kernel
def originalMap : Fin 10 ↪ Fin 12 where
  toFun i := ![0,1,2,5,6,7,8,9,10,11] i
  inj' := by decide +kernel
noncomputable def program : OracleBlock 11 := seq (WordArray.readOn leftRead)
  (seq (WordArray.readOn rightRead) (seq (ArraySwap.on partnerMap) (ArraySwap.on originalMap)))
noncomputable def undo : OracleBlock 11 := seq (ArraySwap.on originalMap) (ArraySwap.on partnerMap)

lemma swap_bound (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    ArraySwap.bound (Switch.rowWords π) a.val b.val≤10000*(n+1)^4 := by
  have hl := Switch.rows_encoded_length (fun i => (π i).val) (fun i => (π i).isLt.le)
  have hh := arraySwap_bound (Switch.rowWords π) a.val b.val
  have ha := a.isLt
  have hb := b.isLt
  have hbase : (encodeBitList (Switch.rowWords π)).length+a.val+b.val+1≤5*(n+1)^2 := by
    change (encodeBitList (Switch.rowWords π)).length≤2*n*n+2*n at hl
    nlinarith
  have hp := Nat.pow_le_pow_left hbase 2
  nlinarith

lemma original_executes (g : BitString → ℕ) (π : Equiv.Perm (Fin n)) (a b : Fin n) (left right : BitString) :
    ∃t,(ArraySwap.on originalMap).Executes g (state (Output.witness π) a.val b.val left right)
      (state (Output.witness (MonotoneEndpoints.transpose π a b)) a.val b.val left right) t ∧
      t≤10000*(n+1)^4 := by
  obtain ⟨t,ht,hb⟩ := ArraySwap.program_executes g (Switch.rowWords π) a.val b.val
  rw [Switch.exchange_rowWords] at ht
  refine ⟨t,?_,hb.trans (swap_bound π a b)⟩
  apply rename_executes_to ArraySwap.program originalMap g ht
  · funext r;fin_cases r <;> rfl
  · funext r;fin_cases r <;> rfl
  · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl)

lemma partner_executes (g : BitString → ℕ) (π : Equiv.Perm (Fin n)) (a b : ℕ) (left right : Fin n) :
    ∃t,(ArraySwap.on partnerMap).Executes g (state (Output.witness π) a b (unary left.val) (unary right.val))
      (state (Output.witness (MonotoneEndpoints.transpose π left right)) a b (unary left.val) (unary right.val)) t ∧
      t≤10000*(n+1)^4 := by
  obtain ⟨t,ht,hb⟩ := ArraySwap.program_executes g (Switch.rowWords π) left.val right.val
  rw [Switch.exchange_rowWords] at ht
  refine ⟨t,?_,hb.trans (swap_bound π left right)⟩
  apply rename_executes_to ArraySwap.program partnerMap g ht
  · funext r;fin_cases r <;> rfl
  · funext r;fin_cases r <;> rfl
  · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl)

theorem program_executes (g : BitString → ℕ) (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    ∃t,program.Executes g (state (Output.witness π) a.val b.val [] [])
      (state (Output.witness (candidate π a b)) a.val b.val (unary (π a).val) (unary (π b).val)) t ∧
      t≤100000*(n+1)^4 := by
  obtain ⟨c1,h1,b1⟩ := WordArray.readOn_executes leftRead g (state (Output.witness π) a.val b.val [] []) (Switch.rowWords π) a.val
    (by funext r;fin_cases r <;> rfl)
  rw [Switch.rowWords_get] at h1
  have e1 : Function.update (state (Output.witness π) a.val b.val [] []) (leftRead 2) (unary (π a).val)=
      state (Output.witness π) a.val b.val (unary (π a).val) [] := by funext r;fin_cases r <;> rfl
  rw [e1] at h1
  obtain ⟨c2,h2,b2⟩ := WordArray.readOn_executes rightRead g
    (state (Output.witness π) a.val b.val (unary (π a).val) []) (Switch.rowWords π) b.val
    (by funext r;fin_cases r <;> rfl)
  rw [Switch.rowWords_get] at h2
  have e2 : Function.update (state (Output.witness π) a.val b.val (unary (π a).val) []) (rightRead 2) (unary (π b).val)=
      state (Output.witness π) a.val b.val (unary (π a).val) (unary (π b).val) := by funext r;fin_cases r <;> rfl
  rw [e2] at h2
  obtain ⟨c3,h3,b3⟩ := partner_executes g π a.val b.val (π a) (π b)
  obtain ⟨c4,h4,b4⟩ := original_executes g (MonotoneEndpoints.transpose π (π a) (π b)) a b (unary (π a).val) (unary (π b).val)
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  have hl := Switch.rows_encoded_length (fun i => (π i).val) (fun i => (π i).isLt.le)
  change (encodeBitList (Switch.rowWords π)).length≤2*n*n+2*n at hl
  have ha := a.isLt
  have hb := b.isLt
  have ham := Nat.mul_le_mul_left a.val hl
  have hbm := Nat.mul_le_mul_left b.val hl
  have ha2 := Nat.mul_le_mul_right (2*n*n+2*n) ha.le
  have hb2 := Nat.mul_le_mul_right (2*n*n+2*n) hb.le
  unfold GraphReduction.Runtime.lookupBound at b1 b2
  nlinarith

lemma undo_executes (g : BitString → ℕ) (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    ∃t,undo.Executes g
      (state (Output.witness (candidate π a b)) a.val b.val (unary (π a).val) (unary (π b).val))
      (state (Output.witness π) a.val b.val (unary (π a).val) (unary (π b).val)) t ∧
      t≤20000*(n+1)^4+2 := by
  obtain ⟨a1,h1,b1⟩ := original_executes g (candidate π a b) a b (unary (π a).val) (unary (π b).val)
  have he : MonotoneEndpoints.transpose (candidate π a b) a b=MonotoneEndpoints.transpose π (π a) (π b) :=
    MonotoneEndpoints.transpose_involutive a b _
  rw [he] at h1
  obtain ⟨a2,h2,b2⟩ := partner_executes g (MonotoneEndpoints.transpose π (π a) (π b)) a.val b.val (π a) (π b)
  have he2 : MonotoneEndpoints.transpose (MonotoneEndpoints.transpose π (π a) (π b)) (π a) (π b)=π :=
    MonotoneEndpoints.transpose_involutive (π a) (π b) π
  rw [he2] at h2
  exact ⟨_,seq_executes _ _ g h1 h2,by omega⟩

lemma candidate_apply (π : Equiv.Perm (Fin n)) (hp : Function.Involutive π) (a b x : Fin n) :
    candidate π a b x=Equiv.swap a b (π (Equiv.swap a b x)) := by
  have hh := π.injective.swap_apply (π a) (π b) (Equiv.swap a b x)
  simpa only [candidate,MonotoneEndpoints.transpose_apply,hp a,hp b] using hh.symm

lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (WordArray.readOn_queryFree _)
  (seq_queryFree _ _ (WordArray.readOn_queryFree _) (seq_queryFree _ _ (ArraySwap.on_queryFree _) (ArraySwap.on_queryFree _)))
lemma undo_queryFree : undo.QueryFree := seq_queryFree _ _ (ArraySwap.on_queryFree _) (ArraySwap.on_queryFree _)

end HiddenCircuits.Approximation.SamplerRuntime.PartnerConjugation
