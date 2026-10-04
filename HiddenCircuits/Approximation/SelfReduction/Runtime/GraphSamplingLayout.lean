import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSamplingGroupLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.BranchSelect
import HiddenCircuits.Approximation.SelfReduction.Runtime.SamplingStage

/-! One complete literal sampling/counting deletion stage. Fresh random blocks
are consumed, real sampler calls are executed, and the empirical maximum is
returned. Persistent graph context and every global unary parameter survive. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def stageSamplePorts : Fin 95 ↪ Fin 99 where
  toFun i := ⟨if i.val < 62 then i.val else i.val+3, by split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun x : Fin 99 => x.val) h
    dsimp at hh
    split_ifs at hh <;> omega

def stageBranchPorts : Fin 21 ↪ Fin 99 where
  toFun i := (Runtime.stageBranchPorts i).castAdd 34
  inj' := by
    intro i j h
    apply Runtime.stageBranchPorts.injective
    exact Fin.ext (congrArg (fun x : Fin 99 => x.val) h)

def stageStore (coins context : BitString) (width batch radius cap groups clock : ℕ)
    (matrix : BitString) (value idx : ℕ) : Store 98 := fun i =>
  if i.val=0 then coins else if i.val=1 then context else if i.val=2 then List.replicate width true
  else if i.val=6 then matrix else if i.val=7 then List.replicate value true
  else if i.val=8 then List.replicate idx true else if i.val=59 then List.replicate batch true
  else if i.val=60 then List.replicate clock true else if i.val=62 then List.replicate radius true
  else if i.val=63 then List.replicate cap true else if i.val=64 then List.replicate groups true else []

/-- The original logical data ports are retained exactly. -/
theorem stageStore_low (coins context : BitString) (width batch radius cap groups clock : ℕ)
    (matrix : BitString) (value idx : ℕ) (i : Fin 65) :
    stageStore coins context width batch radius cap groups clock matrix value idx (i.castAdd 34)=
      Runtime.stageStore coins context width batch radius cap groups clock matrix value idx i := rfl

/-- Every additional general-sampler scratch port is initially and finally clean. -/
theorem stageStore_high (coins context : BitString) (width batch radius cap groups clock : ℕ)
    (matrix : BitString) (value idx : ℕ) (i : Fin 99) (hi : 65 ≤ i.val) :
    stageStore coins context width batch radius cap groups clock matrix value idx i=[] := by
  have hn (n : ℕ) (h : n < 65) : i.val ≠ n := by omega
  simp [stageStore, hn 0 (by decide), hn 1 (by decide), hn 2 (by decide),
    hn 6 (by decide), hn 7 (by decide), hn 8 (by decide), hn 59 (by decide),
    hn 60 (by decide), hn 62 (by decide), hn 63 (by decide), hn 64 (by decide)]

noncomputable def stage : OracleBlock 98 :=
  seq (copyOn 64 60 3 (by decide) (by decide) (by decide))
    (seq (rename sampleGroups stageSamplePorts)
      (seq (copyOn 63 60 3 (by decide) (by decide) (by decide))
        (seq (push 7 true) (seq (rename branchSelect stageBranchPorts) (clear 6)))))

noncomputable def stageBound (C b n width M B radius dataLength : ℕ) : ℕ :=
  (n+1)*sampleGroupBound C width M B+4*(n+1)*(2*M*(B+1)+1)+4+
  ((b+1)*branchIterationBound n M B radius (b+1) dataLength+
    4*(b+1)*(M+1)+(b+1)*(50*(M+b+2))+2*b+16)+
    5*(n+1)+5*(b+1)+dataLength+16

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
