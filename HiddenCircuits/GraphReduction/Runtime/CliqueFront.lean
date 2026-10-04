import HiddenCircuits.GraphReduction.Runtime.CliqueFrontParts

namespace HiddenCircuits.GraphReduction.Runtime.CliqueFront
open Complexity OracleBlock BinaryArithmetic DescriptorFront WordGraph
set_option maxHeartbeats 900000

def records {p : ℕ} (mode : Bool) (ps : List (CutPair p)) (S T : BitString) (s : ℕ) : List VertexRecord :=
  DescriptorEven.records (2*p) ps.length S T ++ DescriptorOdd.records (2*p) 0 ps ++
  DescriptorRectangle.records (taggedVertex false true 0) s (ps.length+1) ++ tailRecords mode s ps.length

def descriptor {p : ℕ} (mode : Bool) (ps : List (CutPair p)) (S T : BitString) (s : ℕ) : BitString :=
  encodeBitList ((records mode ps S T s).map encodeVertex)
noncomputable def body (mode : Bool) : OracleBlock 19 := seq DescriptorEven.program
  (seq DescriptorOdd.program (seq evenProbes (tail mode)))
noncomputable def program (mode : Bool) : OracleBlock 19 := seq (prepend 0 [false,false,false,false,false,false])
  (seq (body mode) (seq (clear 0) (reverseOn 4 18 (by decide))))

def bound (width height samples descriptorLength : ℕ) : ℕ :=
  DescriptorEven.bound width height+5*height+6+
  (height*(width*(20*height+34*width+125)+8*width+128)+4)+
  probeBound (height+1) samples+probeBound height samples+2*descriptorLength+47

lemma body_executes {p : ℕ} (g : BitString → ℕ) (mode : Bool) (ps : List (CutPair p)) (S T : BitString) (s : ℕ)
    (hS : S.length=2*p) (hT : T.length=2*p) :
    ∃c,(body mode).Executes g (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T (pairStream ps) [] 0)
      (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T [] (descriptor mode ps S T s).reverse (records mode ps S T s).length) c ∧
      c≤DescriptorEven.bound (2*p) ps.length+5*ps.length+6+
        (ps.length*((2*p)*(20*ps.length+34*(2*p)+125)+8*(2*p)+128)+4)+
        probeBound (ps.length+1) s+probeBound ps.length s+14 := by
  let A := DescriptorEven.records (2*p) ps.length S T
  let B := DescriptorOdd.records (2*p) 0 ps
  let C := DescriptorRectangle.records (taggedVertex false true 0) s (ps.length+1)
  let outA := (encodeBitList (A.map encodeVertex)).reverse
  let outB := (encodeBitList (B.map encodeVertex)).reverse++outA
  let outC := (encodeBitList (C.map encodeVertex)).reverse++outB
  obtain ⟨a,ha,hab⟩ := DescriptorEven.program_executes g (2*p) ps.length s S T (pairStream ps) [] 0 hS hT
  simp only [List.append_nil,Nat.zero_add] at ha
  obtain ⟨b,hb,hbb⟩ := DescriptorOdd.program_executes g ps ps.length s S T outA A.length
  obtain ⟨c,hc,hcb⟩ := evenProbes_executes g (2*p) ps.length s S T [] outB (A.length+2*p*ps.length)
  obtain ⟨d,hd,hdb⟩ := tail_executes g mode (2*p) ps.length s S T [] outC (A.length+2*p*ps.length+s*(ps.length+1))
  have hall := seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd))
  refine ⟨a+(b+(c+d+2)+2)+2,?_,by omega⟩
  convert hall using 1
  simp only [descriptor,records,List.map_append,encodeBitList_append,List.reverse_append,List.append_assoc,List.length_append]
  dsimp only [outC,outB,outA,A,B,C] at *
  rw [DescriptorOdd.records_length,DescriptorRectangle.records_length]
  simp only [Nat.add_assoc]

 theorem program_executes {p : ℕ} (g : BitString → ℕ) (mode : Bool) (ps : List (CutPair p)) (S T : BitString) (s : ℕ)
    (hS : S.length=2*p) (hT : T.length=2*p) :
    ∃c,(program mode).Executes g (DescriptorFront.state (2*p) ps.length s 0 S T (pairStream ps) [] [] [])
      (DescriptorFront.state (2*p) ps.length s (records mode ps S T s).length S T [] [] (descriptor mode ps S T s) []) c ∧
      c≤bound (2*p) ps.length s (descriptor mode ps S T s).length := by
  have hs : (prepend (0:Fin 20) [false,false,false,false,false,false]).Executes g
      (DescriptorFront.state (2*p) ps.length s 0 S T (pairStream ps) [] [] [])
      (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T (pairStream ps) [] 0) 19 := by
    convert prepend_executes g (0:Fin 20) [false,false,false,false,false,false]
      (DescriptorFront.state (2*p) ps.length s 0 S T (pairStream ps) [] [] []) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hc,hb⟩ := body_executes g mode ps S T s hS hT
  let n := (records mode ps S T s).length
  let desc := descriptor mode ps S T s
  have ht : (clear (0:Fin 20)).Executes g
      (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T [] desc.reverse n)
      (DescriptorFront.state (2*p) ps.length s n S T [] desc.reverse [] []) 7 := by
    convert clear_executes g (0:Fin 20)
      (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T [] desc.reverse n) using 1
    funext i;fin_cases i <;> rfl
  have hr : (reverseOn (4:Fin 20) 18 (by decide)).Executes g
      (DescriptorFront.state (2*p) ps.length s n S T [] desc.reverse [] [])
      (DescriptorFront.state (2*p) ps.length s n S T [] [] desc []) (2*desc.length+1) := by
    convert reverseOn_executes g (4:Fin 20) 18 (by decide) (DescriptorFront.state (2*p) ps.length s n S T [] desc.reverse [] []) using 1
    · funext i;fin_cases i <;> simp [DescriptorFront.state]
    · simp [DescriptorFront.state]
  exact ⟨_,seq_executes _ _ g hs (seq_executes _ _ g hc (seq_executes _ _ g ht hr)),by unfold bound;dsimp only [desc];omega⟩

lemma program_queryFree (mode : Bool) : (program mode).QueryFree := seq_queryFree _ _ (prepend_queryFree _ _)
  (seq_queryFree _ _ (seq_queryFree _ _ DescriptorEven.program_queryFree
    (seq_queryFree _ _ DescriptorOdd.program_queryFree (seq_queryFree _ _ evenProbes_queryFree (tail_queryFree _))))
    (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))
end HiddenCircuits.GraphReduction.Runtime.CliqueFront
