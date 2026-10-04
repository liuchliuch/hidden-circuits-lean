import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointStage
import HiddenCircuits.Approximation.SelfReduction.Runtime.ContextPrepare
import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualProgram

/-! The actual counting loop frame: the 65-stack complete sampling stage plus
current endpoint bytes, precision, remaining depth, count stream and failure bit. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock

def countStagePorts : Fin 65 ↪ Fin 71 where
  toFun i := i.castAdd 6
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 71 => x.val) h)
def countExtraPorts : Fin 6 ↪ Fin 71 where
  toFun i := i.natAdd 65
  inj' := by intro i j h; apply Fin.ext; have hh := congrArg (fun x : Fin 71 => x.val) h; simp at hh; omega

def countFrame (stage : Store 64) (graph : BitString) (T depth : ℕ) (out alive : BitString) : Store 70 :=
  Fin.addCases (m:=65) (n:=6) stage (fun i =>
    if i.val=0 then graph else if i.val=1 then List.replicate T true
    else if i.val=2 then List.replicate depth true else if i.val=3 then out
    else if i.val=5 then alive else [])

@[simp] theorem countFrame_stage (stage : Store 64) (graph : BitString) (T depth : ℕ) (out alive : BitString)
    (i : Fin 65) : countFrame stage graph T depth out alive (countStagePorts i)=stage i := by
  simp [countFrame,countStagePorts]
@[simp] theorem countFrame_extra (stage : Store 64) (graph : BitString) (T depth : ℕ) (out alive : BitString)
    (i : Fin 6) : countFrame stage graph T depth out alive (countExtraPorts i)=
      (if i.val=0 then graph else if i.val=1 then List.replicate T true
      else if i.val=2 then List.replicate depth true else if i.val=3 then out else if i.val=5 then alive else []) := by
  simp [countFrame,countExtraPorts]

 theorem countFrame_ext {s t : Store 70} (hs : ∀ i, s (countStagePorts i)=t (countStagePorts i))
    (he : ∀ i, s (countExtraPorts i)=t (countExtraPorts i)) : s=t := by
  funext i
  exact Fin.addCases (m:=65) (n:=6) hs he i

 theorem countFrame_rename {B : OracleBlock 64} (g : BitString → ℕ) (s t : Store 64) (cost : ℕ)
    (h : B.Executes g s t cost) (graph : BitString) (T depth : ℕ) (out alive : BitString) :
    (rename B countStagePorts).Executes g (countFrame s graph T depth out alive)
      (countFrame t graph T depth out alive) cost := by
  apply rename_executes_to B countStagePorts g h
  · funext i; simp
  · funext i; simp
  · intro j
    refine Fin.addCases (m:=65) (n:=6) (fun i => ?_) (fun i => ?_) j
    · intro hj; exact False.elim (hj i rfl)
    · intro hj; simp [countFrame]

/-- Numeric ports agree with the split frame, reducing only the six control
ports rather than repeatedly expanding a 71-coordinate definition. -/
@[simp] theorem countStagePorts_val (i : Fin 65) : (countStagePorts i).val=i.val := rfl
@[simp] theorem countExtraPorts_val (i : Fin 6) : (countExtraPorts i).val=65+i.val := rfl

def countStore (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) : Store 70 :=
  countFrame (stageStore coins context width batch (8*T) cap groups 0 [] value idx) graph T depth out alive

@[simp] theorem countStore_port0 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 0=coins := rfl
@[simp] theorem countStore_port1 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 1=context := rfl
@[simp] theorem countStore_port2 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 2=List.replicate width true := rfl
@[simp] theorem countStore_port6 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 6=[] := rfl
@[simp] theorem countStore_port7 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 7=List.replicate value true := rfl
@[simp] theorem countStore_port8 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 8=List.replicate idx true := rfl
@[simp] theorem countStore_port59 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 59=List.replicate batch true := rfl
@[simp] theorem countStore_port60 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 60=[] := rfl
@[simp] theorem countStore_port62 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 62=List.replicate (8*T) true := rfl
@[simp] theorem countStore_port63 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 63=List.replicate cap true := rfl
@[simp] theorem countStore_port64 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 64=List.replicate groups true := rfl
@[simp] theorem countStore_port65 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 65=graph := rfl
@[simp] theorem countStore_port66 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 66=List.replicate T true := rfl
@[simp] theorem countStore_port67 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 67=List.replicate depth true := rfl
@[simp] theorem countStore_port68 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 68=out := rfl
@[simp] theorem countStore_port69 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 69=[] := rfl
@[simp] theorem countStore_port70 (coins context graph : BitString) (width batch T cap groups depth : ℕ)
    (out alive : BitString) (value idx : ℕ) :
    countStore coins context graph width batch T cap groups depth out alive value idx 70=alive := rfl

def countContextPorts : Fin 5 ↪ Fin 71 where
  toFun i := ![65,66,1,3,4] i
  inj' := by decide +kernel

def countResidualPorts : Fin 12 ↪ Fin 71 where
  toFun i := ![65,3,4,5,8,9,10,11,12,13,14,15] i
  inj' := by decide +kernel

noncomputable def countPrepare : OracleBlock 70 := rename contextPrepare countContextPorts
noncomputable def countStage : OracleBlock 70 := rename samplingStage countStagePorts
noncomputable def countResidual : OracleBlock 70 := EndpointResidual.programOn countResidualPorts
noncomputable def countAccept : OracleBlock 70 :=
  seq (push 7 true) (seq (emitUnaryReversed 7 68)
    (seq countResidual (seq (clear 8) (clear 1))))
noncomputable def countReject : OracleBlock 70 := seq (clear 67) (seq (clear 70) (seq (clear 8) (clear 1)))
noncomputable def countDecision : OracleBlock 70 := branchPop 7 countReject countAccept countAccept
noncomputable def countBody : OracleBlock 70 := seq countPrepare (seq countStage countDecision)
noncomputable def countLoop : OracleBlock 70 := whilePop 67 countBody countBody

end HiddenCircuits.Approximation.SelfReduction.Runtime
