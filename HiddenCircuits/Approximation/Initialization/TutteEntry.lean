import HiddenCircuits.Approximation.Initialization.WordMatrixLookup
import HiddenCircuits.Approximation.Initialization.TutteInteger
import HiddenCircuits.GraphReduction.Runtime.UnaryCompare
import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits
import HiddenCircuits.Complexity.MatrixEmitter
import HiddenCircuits.Approximation.SamplerRuntime.PartnerEdge

/-! A fixed signed Tutte entry callback. It reads a real graph bit,
compares the row and column, looks up the unordered edge's canonical random
word, and attaches the correct sign including the unique representation of zero. -/
namespace HiddenCircuits.Approximation.Initialization.TutteEntry
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic GraphVerifier.Runtime

def params (payload data : BitString) : Store 20 := fun r =>
  if r.val=8 then payload else if r.val=9 then data else []
def state (n i j : ℕ) (payload data bit out inner outer flag : BitString) : Store 20 :=
  Function.update (MatrixEmitter.store n i j bit out inner outer (params payload data)) 10 flag

def edgePorts : Fin 9 ↪ Fin 21 where
  toFun r := if r.val<3 then ⟨r.val,by omega⟩ else if r.val=3 then 8 else if r.val=4 then 10
    else ⟨r.val+6,by omega⟩
  inj' := by decide +kernel
def comparePorts : Fin 6 ↪ Fin 21 where
  toFun r := if r.val=0 then 1 else if r.val=1 then 2 else if r.val=2 then 10
    else ⟨r.val+8,by omega⟩
  inj' := by decide +kernel
def wordPorts (negative : Bool) : Fin 13 ↪ Fin 21 where
  toFun r := if r.val=0 then 0 else if r.val=1 then (if negative then 2 else 1)
    else if r.val=2 then (if negative then 1 else 2) else if r.val=3 then 9
    else if r.val=4 then 3 else ⟨r.val+6,by omega⟩
  inj' := by cases negative <;> decide +kernel

noncomputable def signed (negative : Bool) : OracleBlock 20 :=
  seq (WordMatrixLookup.on (wordPorts negative)) (finishOn 3 negative)
noncomputable def choose : OracleBlock 20 := branchPop 10 (push 3 false) (signed true) (signed false)
noncomputable def accepted : OracleBlock 20 := seq (GraphReduction.Runtime.readOnlyLTOn comparePorts) choose
noncomputable def program : OracleBlock 20 := seq (matrixLookupOn edgePorts)
  (branchPop 10 (push 3 false) (push 3 false) accepted)

theorem signed_executes (g : BitString → ℕ) (n i j : ℕ) (payload : BitString)
    (ws : List BitString) (out inner outer : BitString) (negative : Bool) :
    ∃ t, (signed negative).Executes g (state n i j payload (encodeBitList ws) [] out inner outer [])
      (state n i j payload (encodeBitList ws)
        (finishSigned negative (ws[(if negative then i+n*j else j+n*i)]?.getD [])) out inner outer []) t ∧
      t ≤ WordMatrixLookup.timeBound n (if negative then j else i) (if negative then i else j)
        (encodeBitList ws).length+5 := by
  obtain ⟨t,ht,hb⟩ := WordMatrixLookup.on_executes (wordPorts negative) g
    (state n i j payload (encodeBitList ws) [] out inner outer []) n
    (if negative then j else i) (if negative then i else j) ws
    (by cases negative <;> funext r <;> fin_cases r <;>
      simp [state,params,wordPorts,MatrixEmitter.store,MatrixEmitter.port,WordMatrixLookup.state])
  let w := ws[(if negative then i+n*j else j+n*i)]?.getD []
  have h1 : (WordMatrixLookup.on (wordPorts negative)).Executes g
      (state n i j payload (encodeBitList ws) [] out inner outer [])
      (state n i j payload (encodeBitList ws) w out inner outer []) t := by
    convert ht using 1
    cases negative <;> funext r <;> fin_cases r <;>
      simp [state,params,wordPorts,MatrixEmitter.store,MatrixEmitter.port,w]
  have h2 : (finishOn (3 : Fin 21) negative).Executes g
      (state n i j payload (encodeBitList ws) w out inner outer [])
      (state n i j payload (encodeBitList ws) (finishSigned negative w) out inner outer []) (finishCost w) := by
    convert finishOn_executes g (3 : Fin 21) negative _ using 1
    · funext r;fin_cases r <;> simp [state,params,MatrixEmitter.store,MatrixEmitter.port]
  refine ⟨_,seq_executes _ _ g h1 h2,?_⟩
  have hh := finishCost_le w
  omega

theorem pop_flag (n i j : ℕ) (payload data bit out inner outer : BitString) (b : Bool) :
    Function.update (state n i j payload data bit out inner outer [b]) 10 [] =
      state n i j payload data bit out inner outer [] := by
  funext r;fin_cases r <;> simp [state]

def randomWords {n : ℕ} (x : Fin (n*n) → ℕ) : List BitString := List.ofFn (fun e => Computability.encodeNat (x e))

theorem program_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixGraph n)
    (x : Fin (n*n) → ℕ) (i j : Fin n) (out inner outer : BitString) :
    ∃ t, program.Executes g
      (state n i.val j.val G.bits (encodeBitList (randomWords x)) [] out inner outer [])
      (state n i.val j.val G.bits (encodeBitList (randomWords x))
        (signedBits (TuttePolynomial.matrix G.graph (fun e => (x e : ℤ)) i j)) out inner outer []) t ∧
      t ≤ 500*(n+(encodeBitList (randomWords x)).length+1)^3 := by
  let D := encodeBitList (randomWords x)
  let z := TuttePolynomial.matrix G.graph (fun e => (x e : ℤ)) i j
  have he := matrixLookupOn_executes edgePorts g (state n i.val j.val G.bits D [] out inner outer [])
    n i.val j.val G.bits
    (by funext r;fin_cases r <;> simp [state,params,edgePorts,MatrixEmitter.store,MatrixEmitter.port,matrixStore])
  rw [SamplerRuntime.PartnerEdge.matrix_bit] at he
  have h1 : (matrixLookupOn edgePorts).Executes g (state n i.val j.val G.bits D [] out inner outer [])
      (state n i.val j.val G.bits D [] out inner outer [G.edge i j]) (matrixLookupCost n i.val j.val G.bits) := by
    convert he using 1
    funext r;fin_cases r <;> simp [state,params,edgePorts,MatrixEmitter.store,MatrixEmitter.port]
  have hs (sign : Bool) : ∃ t, (signed sign).Executes g (state n i.val j.val G.bits D [] out inner outer [])
      (state n i.val j.val G.bits D (signedBits (signedNat sign
        (x (if sign then TuttePolynomial.index j i else TuttePolynomial.index i j)))) out inner outer []) t ∧
      t ≤ 200*(n+D.length+1)^3+5 := by
    obtain ⟨t,ht,hb⟩ := signed_executes g n i.val j.val G.bits (randomWords x) out inner outer sign
    have hw : (randomWords x)[(if sign then i.val+n*j.val else j.val+n*i.val)]?.getD [] =
        Computability.encodeNat (x (if sign then TuttePolynomial.index j i else TuttePolynomial.index i j)) := by
      have hij : j.val+n*i.val < n*n := (TuttePolynomial.index i j).isLt
      have hji : i.val+n*j.val < n*n := (TuttePolynomial.index j i).isLt
      cases sign <;> simp [randomWords,TuttePolynomial.index,finProdFinEquiv,hij,hji]
    rw [hw,finishSigned_encode] at ht
    refine ⟨t,ht,?_⟩
    have hh := WordMatrixLookup.timeBound_in_range (L := D.length)
      (show (if sign then j.val else i.val)<n by cases sign <;> simp [i.isLt,j.isLt])
      (show (if sign then i.val else j.val)<n by cases sign <;> simp [i.isLt,j.isLt])
    exact hb.trans (Nat.add_le_add_right hh 5)
  have hbranch : ∃ t, (branchPop (10 : Fin 21) (push 3 false) (push 3 false) accepted).Executes g
      (state n i.val j.val G.bits D [] out inner outer [G.edge i j])
      (state n i.val j.val G.bits D (signedBits z) out inner outer []) t ∧
      t ≤ 200*(n+D.length+1)^3+20*n+30 := by
    by_cases hadj : G.edge i j = true
    · obtain ⟨a,ha,hab⟩ := GraphReduction.Runtime.readOnlyLTOn_executes comparePorts g
        (state n i.val j.val G.bits D [] out inner outer []) i.val j.val
        (by funext r;fin_cases r <;> simp [state,params,comparePorts,MatrixEmitter.store,MatrixEmitter.port,
          GraphReduction.Runtime.compareStore])
      have hc : (GraphReduction.Runtime.readOnlyLTOn comparePorts).Executes g
          (state n i.val j.val G.bits D [] out inner outer [])
          (state n i.val j.val G.bits D [] out inner outer [decide (i.val<j.val)]) a := by
        convert ha using 1
        funext r;fin_cases r <;> simp [state,params,comparePorts,MatrixEmitter.store,MatrixEmitter.port]
      have hchoose : ∃ b, choose.Executes g
          (state n i.val j.val G.bits D [] out inner outer [decide (i.val<j.val)])
          (state n i.val j.val G.bits D (signedBits z) out inner outer []) b ∧ b ≤ 200*(n+D.length+1)^3+7 := by
        by_cases hij : i.val < j.val
        · obtain ⟨b,hb,hbb⟩ := hs false
          have hz : z = signedNat false (x (TuttePolynomial.index i j)) := by
            simp [z,TuttePolynomial.matrix,MatrixGraph.graph,hadj,show i<j from hij,signedNat]
          refine ⟨b+2,?_,by omega⟩
          simp only [if_false,Bool.false_eq_true] at hb
          rw [hz]
          apply branchPop_true (10 : Fin 21) _ _ _ g (rest := []) (by simp [state,hij])
          simpa only [pop_flag] using hb
        · obtain ⟨b,hb,hbb⟩ := hs true
          have hz : z = signedNat true (x (TuttePolynomial.index j i)) := by
            simp [z,TuttePolynomial.matrix,MatrixGraph.graph,hadj,show ¬i<j from hij,signedNat]
          refine ⟨b+2,?_,by omega⟩
          simp only [if_true] at hb
          rw [hz]
          apply branchPop_false (10 : Fin 21) _ _ _ g (rest := []) (by simp [state,hij])
          simpa only [pop_flag] using hb
      obtain ⟨b,hb,hbb⟩ := hchoose
      have hacc := seq_executes _ _ g hc hb
      refine ⟨a+b+4,?_,?_⟩
      · apply branchPop_true (10 : Fin 21) _ _ _ g (rest := []) (by simp [state,hadj])
        simpa only [pop_flag] using hacc
      · have hi := i.isLt;have hj := j.isLt;omega
    · have hf : G.edge i j = false := Bool.eq_false_iff.mpr hadj
      have hz : signedBits z = [false] := by
        have hz0 : z = 0 := by simp [z,TuttePolynomial.matrix,MatrixGraph.graph,hadj]
        rw [hz0]
        rfl
      refine ⟨3,?_,by omega⟩
      rw [hz]
      apply branchPop_false (10 : Fin 21) _ _ _ g (rest := []) (by simp [state,hf])
      rw [pop_flag]
      convert push_executes g (3 : Fin 21) false _ using 1
      funext r;fin_cases r <;> simp [state,params,MatrixEmitter.store,MatrixEmitter.port]
  obtain ⟨b,hb,hbb⟩ := hbranch
  refine ⟨_,seq_executes _ _ g h1 hb,?_⟩
  have hm := matrixLookupCost_bound n i.val j.val G.bits
  have hi := i.isLt
  have hj := j.isLt
  have hmul : n*i.val ≤ n*n := Nat.mul_le_mul_left n hi.le
  nlinarith [Nat.zero_le (D.length^3),Nat.zero_le (n*D.length^2),Nat.zero_le (n^2*D.length)]

theorem signed_queryFree (sign : Bool) : (signed sign).QueryFree := seq_queryFree _ _
  (WordMatrixLookup.on_queryFree _) (finishOn_queryFree _ _)
theorem program_queryFree : program.QueryFree := seq_queryFree _ _ (matrixLookupOn_queryFree _)
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _)
    (seq_queryFree _ _ (GraphReduction.Runtime.readOnlyLTOn_queryFree _)
      (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (signed_queryFree _) (signed_queryFree _))))

end HiddenCircuits.Approximation.Initialization.TutteEntry
