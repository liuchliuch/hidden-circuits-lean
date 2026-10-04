import HiddenCircuits.Circuit.Runtime.GateEmitter

namespace HiddenCircuits.Circuit.Runtime.GateEmitter
open HiddenCircuits.Complexity OracleBlock

/-- The literal existing H/CZ swap word, with the second-wire offset explicit. -/
def swapItems : List (GateTag × Bool) :=
  [(.hadamard,true),(.controlledSign,false),(.hadamard,true),
   (.hadamard,false),(.controlledSign,false),(.hadamard,false),
   (.hadamard,true),(.controlledSign,false),(.hadamard,true)]

noncomputable def itemBlock (item : GateTag × Bool) : OracleBlock 3 := if item.2 then nextAtom item.1 else atom item.1

def itemChunk (p : ℕ) (item : GateTag × Bool) : BitString := chunk item.1 (if item.2 then p+1 else p)
def itemCost (p : ℕ) (item : GateTag × Bool) : ℕ := if item.2 then 14*p+88 else 14*p+68
noncomputable def swap : OracleBlock 3 := sequence (swapItems.map itemBlock)
def swapBits (p : ℕ) : BitString := swapItems.flatMap (itemChunk p)

lemma update_stream (p : ℕ) (stream counter temporary next : BitString) :
    Function.update (store p stream counter temporary) 1 next=store p next counter temporary := by
  funext i;fin_cases i <;> rfl

theorem swap_executes (g : BitString → ℕ) (p : ℕ) (stream : BitString) :
    swap.Executes g (store p stream [] []) (store p ((swapBits p).reverse++stream) [] []) (126*p+711) := by
  have hitem (item : GateTag × Bool) (_ : item∈swapItems) (out : BitString) :
      (itemBlock item).Executes g (Function.update (store p [] [] []) 1 out)
        (Function.update (store p [] [] []) 1 ((itemChunk p item).reverse++out)) (itemCost p item) := by
    simp only [update_stream]
    rcases item with ⟨tag,next⟩
    cases next
    · exact atom_executes g tag p out
    · exact nextAtom_executes g tag p out
  have h := sequence_emit g swapItems itemBlock (itemChunk p) (itemCost p) (store p [] [] []) 1 hitem stream
  convert h using 1
  · rw [update_stream]
  · rw [update_stream];rfl
  · simp [swapItems,itemCost];omega

lemma swap_queryFree : swap.QueryFree := by
  apply sequence_queryFree
  intro B hb
  obtain ⟨item,hi,rfl⟩ := List.mem_map.mp hb
  unfold itemBlock
  split_ifs
  · exact nextAtom_queryFree _
  · exact atom_queryFree _

/-- Exact gate tags and placements of the existing nine-gate swap macro. -/
lemma adjacentSwap_tags {n : ℕ} (i : Fin (n-1)) :
    (adjacentSwapProgram i).gates.map (fun g => (gateTag g,gatePosition g)) =
      swapItems.map (fun item => (item.1,if item.2 then i.val+1 else i.val)) := by
  simp [adjacentSwapProgram,ConstraintProgram.lift,swapLocalProgram,swapLocalCircuit,
    ConstraintGate.place,gateTag,gatePosition,adjacentPlacement,Placement.compose,firstBit,secondBit,fullTwoBits,swapItems]

/-- The machine emits exactly the canonical bytes of the existing logical swap
macro, including the enclosing gate-list framing. -/
theorem swapBits_eq {n : ℕ} (i : Fin (n-1)) :
    swapBits i.val=encodeBitList ((adjacentSwapProgram i).gates.map gateBits) := by
  rw [←chunks_eq]
  have h := congrArg (List.flatMap (fun t : GateTag × ℕ => chunk t.1 t.2)) (adjacentSwap_tags i)
  simpa only [List.flatMap_map,Function.comp_def,swapBits,itemChunk] using h.symm

end HiddenCircuits.Circuit.Runtime.GateEmitter
