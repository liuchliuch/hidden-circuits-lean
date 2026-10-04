import HiddenCircuits.DH.Runtime.BinaryPipeline
import HiddenCircuits.Complexity.OracleMove

/-! The total DH/quasi-chain perfect-matching counter is
compiled from literal fixed finite-stack code into mathlib TM2 polynomial time.
The algorithm's all-input execution is proved independently of its semantic
promise. This is separate from the sharper graph/arithmetic-operation bound. -/
namespace HiddenCircuits.DH.BinaryRuntime
open Complexity OracleBlock Polynomial
set_option maxHeartbeats 1200000

def function : BitString→BitString := Runtime.BinaryModel.function
noncomputable def program : OracleBlock 53 := seq Runtime.BinaryPipeline.core
  (seq (cleanup 2) (moveOn 2 0 53 (by decide) (by decide) (by decide)))
noncomputable def time : Polynomial ℕ :=
  Runtime.BinaryPipeline.coreTime+60*(X+Runtime.BinaryPipeline.coreTime+3)+10

theorem executes (g : BitString→ℕ) (raw : BitString) :
    ∃t,program.Executes g (Function.update (fun _=>[]) 0 raw)
      (Function.update (fun _=>[]) 0 (function raw)) t ∧ t≤time.eval raw.length := by
  obtain ⟨s,c,hc,ho,hcb⟩:=Runtime.BinaryPipeline.core_executes g raw
  have hi:∀q,(Runtime.BinaryPipeline.input raw q).length≤raw.length:=by
    intro q
    by_cases h:q=0
    · subst q;simp [Runtime.BinaryPipeline.input]
    · simp [Runtime.BinaryPipeline.input,h]
  have hs:=hc.stack_bound hi
  obtain ⟨d,hd,hdb⟩:=cleanup_executes g (2:Fin 54) s (raw.length+c) hs
  have hm:(moveOn (2:Fin 54) 0 53 (by decide) (by decide) (by decide)).Executes g
      (Function.update (fun _=>[]) 2 (s 2)) (Function.update (fun _=>[]) 0 (s 2)) (6*(s 2).length+5):=by
    convert moveOn_executes g (2:Fin 54) 0 53 (by decide) (by decide) (by decide)
      (Function.update (fun _=>[]) 2 (s 2)) rfl using 1
    funext q;fin_cases q <;> simp
  have hh:=seq_executes _ _ g hc (seq_executes _ _ g hd hm)
  rw [ho] at hh
  refine ⟨_,hh,?_⟩
  have hl:=hs (2:Fin 54)
  change (s (2:Fin 54)).length≤raw.length+c at hl
  rw [ho] at hl
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

lemma queryFree : program.QueryFree := seq_queryFree _ _ Runtime.BinaryPipeline.core_queryFree
  (seq_queryFree _ _ (cleanup_queryFree _) (moveOn_queryFree _ _ _ _ _ _))

theorem runs (g : BitString→ℕ) (raw : BitString) :
    ∃t,program.machine.Runs g (program.machine.init raw)
      (program.config program.exit (Function.update (fun _=>[]) 0 (function raw))) t ∧ t≤time.eval raw.length := by
  obtain ⟨t,ht,hb⟩:=executes g raw
  refine ⟨t,(OracleMachine.runs_iff_steps_halt _).mpr ⟨ht,?_⟩,hb⟩
  simp [OracleMachine.step,machine,config,program.exit_halt]

theorem polyTime : PolyTime function := by
  apply OracleMachine.polyTime_of_binary program.machine queryFree time
  intro raw
  obtain ⟨t,ht,hb⟩:=runs (fun _=>0) raw
  refine ⟨_,t,ht,?_,?_,hb⟩
  · rfl
  · intro q hq
    change Function.update (fun _ : Fin 54=>([]:BitString)) 0 (function raw) q=[]
    exact Function.update_of_ne hq _ _

theorem malformed {raw : BitString} (h : GraphInput.decode raw=none) : function raw=[] :=
  Runtime.BinaryModel.malformed h

theorem distanceHereditary (G : GraphInput) (hG : DistanceHereditaryGraph G.2.graph) :
    function (GraphInput.encode G)=Computability.encodeNat (perfectMatchingCount G.2.graph) :=
  Runtime.BinaryModel.distanceHereditary G hG

theorem quasiChains (G : GraphInput) (hG : QuasiChains G.2.graph) :
    function (GraphInput.encode G)=Computability.encodeNat (perfectMatchingCount G.2.graph) :=
  Runtime.BinaryModel.quasiChains G hG

theorem polynomial_counter : ∃f : BitString→BitString,PolyTime f ∧
    (∀G : GraphInput,DistanceHereditaryGraph G.2.graph→f (GraphInput.encode G)=Computability.encodeNat (perfectMatchingCount G.2.graph)) ∧
    (∀G : GraphInput,QuasiChains G.2.graph→f (GraphInput.encode G)=Computability.encodeNat (perfectMatchingCount G.2.graph)) :=
  ⟨function,polyTime,distanceHereditary,quasiChains⟩
end HiddenCircuits.DH.BinaryRuntime
