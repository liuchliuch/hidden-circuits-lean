import HiddenCircuits.Approximation.SelfReduction.Runtime.BranchSelect
import HiddenCircuits.Approximation.SelfReduction.Runtime.StatisticalBridge
import HiddenCircuits.Approximation.SelfReduction.NaturalCounting

/-! The entire finite statistical machine agrees pointwise with the functions
in the sampling-to-counting proof. The shared sample matrix is not an oracle. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity

def sampleMatrix {α : Type*} (b T k : ℕ) (sample : α → Option (Fin (b+1)))
    (r : StageTape α T k) (i : Fin (2*k+1+1)) : List BitString :=
  List.ofFn (fun j => encodePartner (sample (r (Fin.cast (repeatCount_eq k) i) j)))

 theorem sampleMatrix_count {α : Type*} (b T k : ℕ) (sample : α → Option (Fin (b+1)))
    (r : StageTape α T k) (i : Fin (b+1)) (j : Fin (2*k+1+1)) :
    wordOccurrences (List.replicate (i.val+1) true) (sampleMatrix b T k sample r j)=
      eventCount (batchSize T) (fun a => sample a=some i) (r (Fin.cast (repeatCount_eq k) j)) := by
  rw [sampleMatrix,wordOccurrences_ofFn]
  have hi : List.replicate (i.val+1) true=encodePartner (some i) := by simp [encodePartner,List.replicate_succ]
  rw [hi]
  unfold eventCount
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => ((encodePartner_injective b) h).symm,fun h => congrArg encodePartner h.symm⟩

 theorem branchBoostValue_statistical {α : Type*} (b T k : ℕ) (sample : α → Option (Fin (b+1)))
    (r : StageTape α T k) (i : Fin (b+1)) :
    branchBoostValue (2*k+1) (8*T) (sampleMatrix b T k sample r) i.val=
      naturalAmplifiedCount (fun a => sample a=some i) T k r := by
  have hc : (fun j => wordOccurrences (List.replicate (i.val+1) true) (sampleMatrix b T k sample r j))=
      (fun j => eventCount (batchSize T) (fun a => sample a=some i) (r (Fin.cast (repeatCount_eq k) j))) := by
    funext j
    exact sampleMatrix_count b T k sample r i j
  unfold branchBoostValue groupBoostValue
  rw [hc]
  rfl

 theorem branchStatistics_executes {S α : Type*} (b T k : ℕ) (sample : S → α → Option (Fin (b+1)))
    (s : S) (r : StageTape α T k) (g : BitString → ℕ) :
    let groups := sampleMatrix b T k (sample s) r
    let j := naturalSelectedBranch b T k sample s r
    let c := naturalAmplifiedCount (fun a => sample s a=some j) T k r
    ∃ t, branchSelect.Executes g (branchStore 0 (8*T) (b+1) (groupWords (List.ofFn groups)) [] 0)
      (selectedStore c j.val (8*T) (groupWords (List.ofFn groups))) t ∧
      t ≤ (b+1)*branchIterationBound (2*k+1) (batchSize T) (b+1) (8*T) (b+1)
          (groupWords (List.ofFn groups)).length+
        4*(b+1)*(batchSize T+1)+(b+1)*(50*(batchSize T+b+2))+2*b+16 := by
  dsimp only
  have hM (i) : (sampleMatrix b T k (sample s) r i).length ≤ batchSize T := by simp [sampleMatrix]
  have hB (i) : ∀ x ∈ sampleMatrix b T k (sample s) r i, x.length ≤ b+1 := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact encodePartner_length _
  have h := branchSelect_executes g b (2*k+1) (batchSize T) (b+1) (8*T)
    (sampleMatrix b T k (sample s) r) hM hB
  have hc : (fun i : Fin (b+1) => branchBoostValue (2*k+1) (8*T) (sampleMatrix b T k (sample s) r) i.val)=
      (fun i => naturalAmplifiedCount (fun a => sample s a=some i) T k r) := by
    funext i
    exact branchBoostValue_statistical b T k (sample s) r i
  dsimp only at h
  rw [hc] at h
  simpa only [branchBoostValue_statistical,naturalSelectedBranch] using h

end HiddenCircuits.Approximation.SelfReduction.Runtime
