import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualFields
import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserTriple

/-! Raw canonical endpoint-byte entrypoint for the residual emitter. Parsing,
header/row deletion, unary boundary updates and serialization are all charged.
The finite code receives only byte stacks and the unary chosen column. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
open Complexity OracleBlock GraphReduction SamplerRuntime.EndpointFiber SamplerRuntime.EndpointParser

/-- Stack zero holds canonical endpoint bytes; stack four holds the selected
column in unary. All other stacks are empty. -/
def inputStore (xs chosen : BitString) : Store 11 := fieldStore xs [] [] [] chosen []
def rawMap : Fin 8 ↪ Fin 12 where
  toFun i := ![0,1,2,3,10,7,8,9] i
  inj' := by decide +kernel
noncomputable def unpack : OracleBlock 11 := seq (rename tripleBlock rawMap)
  (seq (clear 7) (seq (clear 8) (clear 9)))
noncomputable def program : OracleBlock 11 := seq unpack fieldsProgram

lemma unpack_executes (g : BitString  →  ℕ) (a b c chosen : BitString) :
    ∃cost, unpack.Executes g (inputStore (encodeBitList [a,b,c]) chosen)
      (fieldStore [] a b c chosen []) cost ∧ cost ≤ 9*(encodeBitList [a,b,c]).length+34 := by
  let s := fieldStore [] a b c chosen []
  let s1 := Function.update (Function.update (Function.update s 7 [true]) 8 [true]) 9 [true]
  let s2 := Function.update (Function.update s 8 [true]) 9 [true]
  let s3 := Function.update s 9 [true]
  have h1 : (rename tripleBlock rawMap).Executes g (inputStore (encodeBitList [a,b,c]) chosen) s1
      (tripleCost (encodeBitList [a,b,c])) := by
    apply rename_executes_to tripleBlock rawMap g (triple_executes g (encodeBitList [a,b,c]))
    · funext i;fin_cases i <;> rfl
    · rw [tripleResult_encode]
      funext i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim | exact (hi 5 rfl).elim | exact (hi 6 rfl).elim | exact (hi 7 rfl).elim
  have h2 : (clear (7:Fin 12)).Executes g s1 s2 2 := by
    convert clear_executes g (7:Fin 12) s1 using 1
    funext i;fin_cases i <;> rfl
  have h3 : (clear (8:Fin 12)).Executes g s2 s3 2 := by
    convert clear_executes g (8:Fin 12) s2 using 1
    funext i;fin_cases i <;> rfl
  have h4 : (clear (9:Fin 12)).Executes g s3 s 2 := by
    convert clear_executes g (9:Fin 12) s3 using 1
    funext i;fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  have hb := triple_cost_bound (encodeBitList [a,b,c])
  omega

/-- A single fixed finite query-free bit program emits the exact canonical
row-zero/column-j residual in explicit polynomial time. No adjacency proof,
retained-mask certificate, arithmetic operation, or encoder is supplied to code. -/
theorem program_executes (g : BitString  →  ℕ) {n : ℕ} (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) :
    ∃cost, program.Executes g
      (inputStore (MonotoneEndpointEncoding.encode ⟨n+1,E⟩) (unary j.val))
      (inputStore (MonotoneEndpointEncoding.encode ⟨n,deleteFirst E j⟩) (unary j.val)) cost ∧
      cost ≤ 1000*(n+2)^2 := by
  obtain ⟨cp,hp,hbp⟩ := unpack_executes g (unary (n+1))
    (encodeBitList (MonotoneEndpointEncoding.rows E.lo))
    (encodeBitList (MonotoneEndpointEncoding.rows E.hi)) (unary j.val)
  obtain ⟨cf,hf,hbf⟩ := fieldsProgram_executes g E j
  refine ⟨_,seq_executes _ _ g hp hf,?_⟩
  have hlen := MonotoneEndpointEncoding.encode_length ⟨n+1,E⟩
  change (MonotoneEndpointEncoding.encode ⟨n+1,E⟩).length ≤ _ at hlen
  change cp ≤ 9*(MonotoneEndpointEncoding.encode ⟨n+1,E⟩).length+34 at hbp
  nlinarith

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (rename_queryFree _ _ triple_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))
  fieldsProgram_queryFree


/-- Uniform polynomial bound in any fixed original branch cap. -/
theorem program_bounded (g : BitString  →  ℕ) {b n : ℕ} (hn : n ≤ b)
    (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) :
    ∃cost, program.Executes g
      (inputStore (MonotoneEndpointEncoding.encode ⟨n+1,E⟩) (unary j.val))
      (inputStore (MonotoneEndpointEncoding.encode ⟨n,deleteFirst E j⟩) (unary j.val)) cost ∧
      cost ≤ 1000*(b+2)^2 := by
  obtain ⟨c,hc,hb⟩ := program_executes g E j
  exact ⟨c,hc,hb.trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (by omega) 2))⟩

noncomputable def programOn {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) : OracleBlock k := rename program φ

/-- Framed entrypoint for a larger sampling/counting program. Only the encoded
endpoint input port changes; the chosen column and every outside port survive. -/
theorem programOn_executes {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) (g : BitString  →  ℕ)
    (s : Store k) {n : ℕ} (E : MonotoneEndpoints (n+1)) (j : Fin (n+1))
    (hs : s∘φ=inputStore (MonotoneEndpointEncoding.encode ⟨n+1,E⟩) (unary j.val)) :
    ∃cost, (programOn φ).Executes g s
      (Function.update s (φ 0) (MonotoneEndpointEncoding.encode ⟨n,deleteFirst E j⟩)) cost ∧
      cost ≤ 1000*(n+2)^2 := by
  obtain ⟨c,hc,hb⟩ := program_executes g E j
  refine ⟨c,?_,hb⟩
  apply rename_executes_to program φ g hc hs
  · funext i
    have he := congrFun hs i
    fin_cases i <;> simp_all [Function.comp_def,Function.update_apply,φ.injective.eq_iff,inputStore,fieldStore]
  · intro i hi
    exact Function.update_of_ne (hi 0).symm _ _
lemma programOn_queryFree {k : ℕ} (φ : Fin 12 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

/-- Count interpretation is explicitly guarded by a legal chosen edge. A
forbidden/padded candidate must use the separate rejected state, never this
smaller active endpoint instance as a replacement for zero. -/
theorem program_fiber_count {n : ℕ} (E : MonotoneEndpoints (n+1)) (j : Fin (n+1))
    (hj : E.lo 0 ≤ j.val ∧ j.val<E.hi 0) :
    MonotoneEndpointEncoding.count (MonotoneEndpointEncoding.encode ⟨n,deleteFirst E j⟩)=
      Fintype.card (Fiber E j) := by
  rw [MonotoneEndpointEncoding.count_encode,card_fiber E j hj]
end HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidual
