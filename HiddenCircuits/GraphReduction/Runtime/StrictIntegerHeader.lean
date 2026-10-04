import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphFront
import HiddenCircuits.Complexity.BinaryArithmetic.CleanOperations
import HiddenCircuits.Complexity.PairSerialization
import HiddenCircuits.Complexity.OraclePrecompose

/-! Actual binary radius-header translation. The input and output contain only
one signed integer header followed by labelled integer coordinate words. -/
namespace HiddenCircuits.GraphReduction.Runtime.StrictIntegerHeader
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000

def delta (subtract : Bool) : ℤ := if subtract then -1 else 1
def bits (subtract : Bool) (xs : BitString) : BitString :=
  true :: pairBits (signedBits (CoordinateGraph.denominator xs + delta subtract))
    (CoordinateGraph.coordinates xs)
def addMap : Fin 7 ↪ Fin 32 where
  toFun i := ![9,27,28,29,30,31,10] i
  inj' := by decide +kernel
def pairMap : Fin 3 ↪ Fin 32 where
  toFun i := ![0,9,27] i
  inj' := by decide +kernel
noncomputable def seed (subtract : Bool) : OracleBlock 31 := seedFlags [(27,true),(27,subtract)]
noncomputable def add : OracleBlock 31 := rename signedAddClean addMap
noncomputable def program (subtract : Bool) : OracleBlock 31 :=
  seq CoordinateGraph.header (seq (SignedNormalize.on CoordinateGraph.denominatorMap)
    (seq (seed subtract) (seq add (seq (PairSerialization.on pairMap) (push 0 true)))))
noncomputable def time : Polynomial ℕ := 100000*(X+1)
noncomputable def size : Polynomial ℕ := X+time

@[simp] lemma signed_delta (b : Bool) : signedBits (delta b)=[b,true] := by cases b <;> rfl

lemma add_executes (g : BitString → ℕ) (data : BitString) (d : ℤ) (b : Bool) :
    ∃c,add.Executes g
      (Function.update (CoordinateGraph.headerOutput data (signedBits d)) 27 (signedBits (delta b)))
      (CoordinateGraph.headerOutput data (signedBits (d+delta b))) c ∧
      c≤400*((signedBits d).length+3) := by
  obtain ⟨c,hc,hb⟩ := cleanAdd_executes g d (delta b)
  refine ⟨c,?_,?_⟩
  · apply rename_executes_to _ addMap g hc
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      have h9 : i.val≠9 := by intro h;exact hi 0 (Fin.ext h.symm)
      have h27 : i≠27 := by intro h;subst i;exact hi 1 rfl
      simp [CoordinateGraph.headerOutput,Function.update_of_ne h27,h9]
  · simpa [cleanAddTime] using hb

lemma program_executes (b : Bool) (g : BitString → ℕ) (xs : BitString) :
    ∃c,(program b).Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (bits b xs)) c ∧c≤time.eval xs.length := by
  let data := CoordinateGraph.coordinates xs
  let raw := LooseWordList.head xs
  let d := CoordinateGraph.denominator xs
  let h0 := CoordinateGraph.headerOutput data raw
  let h1 := CoordinateGraph.headerOutput data (signedBits d)
  let h2 := Function.update h1 (27:Fin 32) (signedBits (delta b))
  let h3 := CoordinateGraph.headerOutput data (signedBits (d+delta b))
  let h4 := Function.update (fun _ : Fin 32=>[]) 0 (pairBits (signedBits (d+delta b)) data)
  obtain ⟨a,ha,hba⟩ := CoordinateGraph.header_executes g xs
  obtain ⟨n,hn,hbn⟩ := SignedNormalize.on_executes CoordinateGraph.denominatorMap g h0 raw
    (by funext i;fin_cases i <;> rfl)
  have hn' : (SignedNormalize.on CoordinateGraph.denominatorMap).Executes g h0 h1 n := by
    convert hn using 1
    funext i;fin_cases i <;> rfl
  have hs : (seed b).Executes g h1 h2 7 := by
    convert seedFlags_executes [(27,true),(27,b)] g h1 using 1
    funext i;fin_cases i <;> simp [seededFlags,h2,h1,CoordinateGraph.headerOutput]
  obtain ⟨c,hc,hbc⟩ := add_executes g data d b
  have hp : (PairSerialization.on pairMap).Executes g h3 h4
      (10*(signedBits (d+delta b)).length+9) := by
    convert PairSerialization.on_executes pairMap g h3 (signedBits (d+delta b)) data
      (by funext i;fin_cases i <;> rfl) using 1
    funext i;fin_cases i <;> rfl
  have hf : (push (0:Fin 32) true).Executes g h4
      (Function.update (fun _=>[]) 0 (bits b xs)) 1 := by
    convert push_executes g (0:Fin 32) true h4 using 1
    funext i;fin_cases i <;> rfl
  have hl := CoordinateGraph.coordinate_length xs
  have hh := CoordinateGraph.head_length xs
  have hd := CoordinateGraph.denominator_length xs
  have hbound : ∀i,(h2 i).length≤data.length+(signedBits d).length+2 := by
    intro i;simp only [h2,h1,CoordinateGraph.headerOutput,Function.update_apply,signed_delta]
    split_ifs <;> (try simp only [List.length_cons,List.length_nil]) <;> omega
  have hout := hc.stack_bound hbound (9:Fin 32)
  change (signedBits (d+delta b)).length≤data.length+(signedBits d).length+2+c at hout
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hn'
    (seq_executes _ _ g hs (seq_executes _ _ g hc (seq_executes _ _ g hp hf)))),?_⟩
  simp only [time,eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  dsimp only [data,raw,d] at *
  omega

lemma program_queryFree (b : Bool) : (program b).QueryFree :=
  seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree
    (seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _) (clear_queryFree _))
    (seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _) (clear_queryFree _)))
    (seq_queryFree _ _ (SignedNormalize.on_queryFree _) (seq_queryFree _ _ (seedFlags_queryFree _)
      (seq_queryFree _ _ (rename_queryFree _ _ signedAddClean_queryFree)
        (seq_queryFree _ _ (PairSerialization.on_queryFree _) (push_queryFree _ _)))))

lemma size_bound (b : Bool) (xs : BitString) : (bits b xs).length≤size.eval xs.length := by
  obtain ⟨c,hc,hb⟩ := program_executes b (fun _=>0) xs
  have h := hc.stack_bound ((program b).machine.init_stack_bound xs) (0:Fin 32)
  change (bits b xs).length≤xs.length+c at h
  simp only [size,eval_add,eval_X]
  omega

@[simp] lemma bits_encode (b : Bool) (r : ℤ) (ws : List BitString) :
    bits b (encodeBitList (signedBits r::ws))=encodeBitList (signedBits (r+delta b)::ws) := by
  simp [bits,CoordinateGraph.denominator,CoordinateGraph.coordinates,LooseWordList.head,
    LooseWordList.tail,encodeBitList]
end HiddenCircuits.GraphReduction.Runtime.StrictIntegerHeader
