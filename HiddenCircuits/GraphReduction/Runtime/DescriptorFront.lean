import HiddenCircuits.GraphReduction.Runtime.DescriptorOddProgram
import HiddenCircuits.GraphReduction.Runtime.DescriptorProbes

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorFront
open Complexity OracleBlock BinaryArithmetic WordGraph
set_option maxHeartbeats 900000

def records {p : ℕ} (ps : List (CutPair p)) (S T : BitString) (s : ℕ) : List VertexRecord :=
  DescriptorEven.records (2*p) ps.length S T ++
  DescriptorRectangle.records (taggedVertex false true 0) s ps.length ++
  DescriptorOdd.records (2*p) 0 ps ++
  DescriptorRectangle.records (taggedVertex true true 0) s ps.length

def descriptor {p : ℕ} (ps : List (CutPair p)) (S T : BitString) (s : ℕ) : BitString :=
  encodeBitList ((records ps S T s).map encodeVertex)

def state (width height samples count : ℕ) (S T pairs out descriptor tag : BitString) : Store 19 := fun i =>
  if i.val=0 then tag else if i.val=4 then out else if i.val=5 then List.replicate count true
  else if i.val=8 then List.replicate width true else if i.val=10 then List.replicate height true
  else if i.val=12 then S else if i.val=13 then T else if i.val=16 then pairs
  else if i.val=17 then List.replicate samples true else if i.val=18 then descriptor else []

noncomputable def body : OracleBlock 19 := seq DescriptorEven.program
  (seq (probes false) (seq DescriptorOdd.program (probes true)))
noncomputable def program : OracleBlock 19 := seq (prepend 0 [false,false,false,false,false,false])
  (seq body (seq (clear 0) (reverseOn 4 18 (by decide))))

def bound (width height samples descriptorLength : ℕ) : ℕ :=
  DescriptorEven.bound width height+5*height+6+
  2*(height*(samples*(20*height+20*samples+125)+19)+68)+
  (height*(width*(20*height+34*width+125)+8*width+128)+4)+2*descriptorLength+39

lemma body_executes {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : BitString) (s : ℕ)
    (hS : S.length=2*p) (hT : T.length=2*p) :
    ∃c,body.Executes g (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T (pairStream ps) [] 0)
      (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T [] (descriptor ps S T s).reverse (records ps S T s).length) c ∧
      c≤DescriptorEven.bound (2*p) ps.length+5*ps.length+6+
        2*(ps.length*(s*(20*ps.length+20*s+125)+19)+68)+
        (ps.length*((2*p)*(20*ps.length+34*(2*p)+125)+8*(2*p)+128)+4)+6 := by
  let A := DescriptorEven.records (2*p) ps.length S T
  let B := DescriptorRectangle.records (taggedVertex false true 0) s ps.length
  let C := DescriptorOdd.records (2*p) 0 ps
  let D := DescriptorRectangle.records (taggedVertex true true 0) s ps.length
  let outA := (encodeBitList (A.map encodeVertex)).reverse
  let outB := (encodeBitList (B.map encodeVertex)).reverse++outA
  let outC := (encodeBitList (C.map encodeVertex)).reverse++outB
  obtain ⟨a,ha,hab⟩ := DescriptorEven.program_executes g (2*p) ps.length s S T (pairStream ps) [] 0 hS hT
  simp only [List.append_nil,Nat.zero_add] at ha
  obtain ⟨b,hb,hbb⟩ := probes_executes g false (2*p) ps.length s S T (pairStream ps) outA A.length
  obtain ⟨c,hc,hcb⟩ := DescriptorOdd.program_executes g ps ps.length s S T outB (A.length+s*ps.length)
  obtain ⟨d,hd,hdb⟩ := probes_executes g true (2*p) ps.length s S T [] outC (A.length+s*ps.length+2*p*ps.length)
  have hall := seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd))
  refine ⟨a+(b+(c+d+2)+2)+2,?_,by omega⟩
  convert hall using 1
  simp only [descriptor,records,List.map_append,encodeBitList_append,List.reverse_append,List.append_assoc,List.length_append]
  dsimp only [outC,outB,outA,A,B,C,D] at *
  rw [DescriptorRectangle.records_length,DescriptorOdd.records_length,DescriptorRectangle.records_length]
  simp only [Nat.add_assoc]

 theorem program_executes {p : ℕ} (g : BitString → ℕ) (ps : List (CutPair p)) (S T : BitString) (s : ℕ)
    (hS : S.length=2*p) (hT : T.length=2*p) :
    ∃c,program.Executes g (state (2*p) ps.length s 0 S T (pairStream ps) [] [] [])
      (state (2*p) ps.length s (records ps S T s).length S T [] [] (descriptor ps S T s) []) c ∧
      c≤bound (2*p) ps.length s (descriptor ps S T s).length := by
  have hs : (prepend (0:Fin 20) [false,false,false,false,false,false]).Executes g
      (state (2*p) ps.length s 0 S T (pairStream ps) [] [] [])
      (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T (pairStream ps) [] 0) 19 := by
    convert prepend_executes g (0:Fin 20) [false,false,false,false,false,false]
      (state (2*p) ps.length s 0 S T (pairStream ps) [] [] []) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hc,hb⟩ := body_executes g ps S T s hS hT
  let n := (records ps S T s).length
  let desc := descriptor ps S T s
  have ht : (clear (0:Fin 20)).Executes g
      (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T [] desc.reverse n)
      (state (2*p) ps.length s n S T [] desc.reverse [] []) 7 := by
    convert clear_executes g (0:Fin 20)
      (workState (DescriptorEven.vertex 0) (2*p) ps.length s 0 [] S T [] desc.reverse n) using 1
    funext i;fin_cases i <;> rfl
  have hr : (reverseOn (4:Fin 20) 18 (by decide)).Executes g
      (state (2*p) ps.length s n S T [] desc.reverse [] [])
      (state (2*p) ps.length s n S T [] [] desc []) (2*desc.length+1) := by
    convert reverseOn_executes g (4:Fin 20) 18 (by decide) (state (2*p) ps.length s n S T [] desc.reverse [] []) using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state]
  exact ⟨_,seq_executes _ _ g hs (seq_executes _ _ g hc (seq_executes _ _ g ht hr)),by unfold bound;dsimp only [desc];omega⟩
end HiddenCircuits.GraphReduction.Runtime.DescriptorFront
