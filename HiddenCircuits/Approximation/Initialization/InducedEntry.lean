import HiddenCircuits.Complexity.MatrixEmitterGraph
import HiddenCircuits.GraphReduction.Runtime.ListLookup
import HiddenCircuits.Approximation.SamplerRuntime.PartnerEdge

/-! Literal adjacency callback for an inherited-order induced graph.
Both retained vertex addresses are read from the real encoded word array. -/
namespace HiddenCircuits.Approximation.Initialization.InducedEntry
open Complexity Complexity.OracleBlock GraphVerifier.Runtime

def params (N : ℕ) (payload data : BitString) : Store 16 := fun r =>
  if r.val=8 then List.replicate N true else if r.val=9 then payload
  else if r.val=10 then data else []
def state (n N i j : ℕ) (payload data bit out inner outer left right : BitString) : Store 16 :=
  Function.update (Function.update (MatrixEmitter.store n i j bit out inner outer
    (params N payload data)) 11 left) 12 right

def rowPorts : Fin 7 ↪ Fin 17 where
  toFun r := if r.val=0 then 10 else if r.val=1 then 1 else if r.val=2 then 11
    else ⟨r.val+10,by omega⟩
  inj' := by decide +kernel
def colPorts : Fin 7 ↪ Fin 17 where
  toFun r := if r.val=0 then 10 else if r.val=1 then 2 else if r.val=2 then 12
    else ⟨r.val+10,by omega⟩
  inj' := by decide +kernel
def edgePorts : Fin 9 ↪ Fin 17 where
  toFun r := if r.val=0 then 8 else if r.val=1 then 11 else if r.val=2 then 12
    else if r.val=3 then 9 else if r.val=4 then 3 else ⟨r.val+8,by omega⟩
  inj' := by decide +kernel

noncomputable def program : OracleBlock 16 :=
  seq (GraphReduction.Runtime.listLookupOn rowPorts)
    (seq (GraphReduction.Runtime.listLookupOn colPorts)
      (seq (matrixLookupOn edgePorts) (seq (clear 11) (clear 12))))

theorem program_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N)
    (ws : List BitString) (n i j : ℕ) (out inner outer : BitString) (u v : Fin N)
    (hi : i < n) (hj : j < n)
    (hu : ws[i]?.getD [] = List.replicate u.val true)
    (hv : ws[j]?.getD [] = List.replicate v.val true) :
    ∃ t, program.Executes g (state n N i j G.bits (encodeBitList ws) [] out inner outer [] [])
      (state n N i j G.bits (encodeBitList ws) [G.edge u v] out inner outer [] []) t ∧
      t ≤ 500*(N+n+(encodeBitList ws).length+1)^2 := by
  obtain ⟨a,ha,hab⟩ := GraphReduction.Runtime.listLookupOn_executes rowPorts g
    (state n N i j G.bits (encodeBitList ws) [] out inner outer [] []) ws i
    (by funext r;fin_cases r <;> simp [state,params,rowPorts,MatrixEmitter.store,MatrixEmitter.port,
      GraphReduction.Runtime.lookupStore])
  rw [hu] at ha
  have h1 : (GraphReduction.Runtime.listLookupOn rowPorts).Executes g
      (state n N i j G.bits (encodeBitList ws) [] out inner outer [] [])
      (state n N i j G.bits (encodeBitList ws) [] out inner outer (List.replicate u.val true) []) a := by
    convert ha using 1
    funext r;fin_cases r <;> simp [state,params,rowPorts,MatrixEmitter.store,MatrixEmitter.port]
  obtain ⟨b,hb,hbb⟩ := GraphReduction.Runtime.listLookupOn_executes colPorts g
    (state n N i j G.bits (encodeBitList ws) [] out inner outer (List.replicate u.val true) []) ws j
    (by funext r;fin_cases r <;> simp [state,params,colPorts,MatrixEmitter.store,MatrixEmitter.port,
      GraphReduction.Runtime.lookupStore])
  rw [hv] at hb
  have h2 : (GraphReduction.Runtime.listLookupOn colPorts).Executes g
      (state n N i j G.bits (encodeBitList ws) [] out inner outer (List.replicate u.val true) [])
      (state n N i j G.bits (encodeBitList ws) [] out inner outer
        (List.replicate u.val true) (List.replicate v.val true)) b := by
    convert hb using 1
    funext r;fin_cases r <;> simp [state,params,colPorts,MatrixEmitter.store,MatrixEmitter.port]
  have he := matrixLookupOn_executes edgePorts g
    (state n N i j G.bits (encodeBitList ws) [] out inner outer
      (List.replicate u.val true) (List.replicate v.val true)) N u.val v.val G.bits
    (by funext r;fin_cases r <;> simp [state,params,edgePorts,MatrixEmitter.store,MatrixEmitter.port,matrixStore])
  rw [SamplerRuntime.PartnerEdge.matrix_bit] at he
  have h3 : (matrixLookupOn edgePorts).Executes g
      (state n N i j G.bits (encodeBitList ws) [] out inner outer
        (List.replicate u.val true) (List.replicate v.val true))
      (state n N i j G.bits (encodeBitList ws) [G.edge u v] out inner outer
        (List.replicate u.val true) (List.replicate v.val true)) (matrixLookupCost N u.val v.val G.bits) := by
    convert he using 1
    funext r;fin_cases r <;> simp [state,params,edgePorts,MatrixEmitter.store,MatrixEmitter.port]
  have h4 : (clear (11 : Fin 17)).Executes g
      (state n N i j G.bits (encodeBitList ws) [G.edge u v] out inner outer
        (List.replicate u.val true) (List.replicate v.val true))
      (state n N i j G.bits (encodeBitList ws) [G.edge u v] out inner outer []
        (List.replicate v.val true)) (u.val+1) := by
    convert clear_executes g (11 : Fin 17) _ using 1
    · funext r;fin_cases r <;> simp [state,params,MatrixEmitter.store,MatrixEmitter.port]
    · simp [state]
  have h5 : (clear (12 : Fin 17)).Executes g
      (state n N i j G.bits (encodeBitList ws) [G.edge u v] out inner outer []
        (List.replicate v.val true))
      (state n N i j G.bits (encodeBitList ws) [G.edge u v] out inner outer [] []) (v.val+1) := by
    convert clear_executes g (12 : Fin 17) _ using 1
    · funext r;fin_cases r <;> simp [state,params,MatrixEmitter.store,MatrixEmitter.port]
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2
    (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  have hm := matrixLookupCost_bound N u.val v.val G.bits
  have hui := u.isLt
  have hvi := v.isLt
  unfold GraphReduction.Runtime.lookupBound at hab hbb
  have hmul : N*u.val ≤ N*N := Nat.mul_le_mul_left N hui.le
  have hmul' : (i+j)*(encodeBitList ws).length ≤ (n+n)*(encodeBitList ws).length :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith [sq_nonneg (N : ℤ),sq_nonneg (n : ℤ)]

theorem program_queryFree : program.QueryFree := seq_queryFree _ _
  (GraphReduction.Runtime.listLookupOn_queryFree _) (seq_queryFree _ _
    (GraphReduction.Runtime.listLookupOn_queryFree _) (seq_queryFree _ _
      (matrixLookupOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))

end HiddenCircuits.Approximation.Initialization.InducedEntry
