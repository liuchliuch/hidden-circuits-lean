import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionRawCore

/-! One actual raw graph→native coordinate machine. Recognition, original-label
ordering, bounded relaxation, binary serialization and cleanup are all executed.
Rejected inputs return []; accepted empty graphs retain their valid denominator. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionRaw
open Complexity Complexity.OracleBlock Polynomial UnitCoordinateExtractionResult

noncomputable def positive : OracleBlock 47:=seq compute (cleanResult 15 45 (by decide) (by decide))
noncomputable def reject : OracleBlock 47:=seq (clear 0) (cleanup 0)
noncomputable def program : OracleBlock 47:=seq UnitOrderProgram.program (branchPop 1 reject reject positive)
noncomputable def time : Polynomial ℕ:=UnitOrderProgram.time+computeTime+
  60*(X+UnitOrderProgram.time+computeTime+3)+10

lemma initial_bound (raw : BitString) : ∀i,(input raw i).length ≤ raw.length:=by
  intro i;simp only [input,UnitOrderProgram.input,Function.update_apply];split_ifs <;> simp
lemma ready_bound (raw : BitString) (B : ℕ) (hB:∀i,(UnitOrderProgram.output raw i).length ≤ B) :
    ∀i,(ready raw i).length ≤ B:=by
  intro i;simp only [ready,Function.update_apply];split_ifs <;> simp_all

lemma positive_executes (g : BitString→ℕ) (raw : BitString) (G : GraphInput)
    (hd:GraphInput.decode raw=some G) (hu:RealUnitInterval.UnitIntervalGraph G.2.graph)
    (B : ℕ) (hB:∀i,(ready raw i).length ≤ B) :
    ∃c,positive.Executes g (ready raw) (input (bytes G)) c ∧
      c ≤ computeTime.eval G.1+52*(B+computeTime.eval G.1+3)+3 := by
  obtain ⟨s,a,ha,hs,hab⟩:=compute_executes g raw G hd hu
  obtain ⟨b,hb,hbb⟩:=cleanResult_executes g (15:Fin 48) 45 (by decide) (by decide) (by decide)
    s (B+a) (ha.stack_bound hB)
  rw [hs] at hb
  exact ⟨_,seq_executes _ _ g ha hb,by omega⟩
lemma reject_executes (g : BitString→ℕ) (s : Store 47) (B : ℕ) (hB:∀i,(s i).length ≤ B) :
    ∃c,reject.Executes g s (input []) c ∧c ≤ 52*(B+3)+3 := by
  have hc:=clear_executes g (0:Fin 48) s
  have hnext:∀i,(Function.update s (0:Fin 48) [] i).length ≤ B:=by
    intro i;simp only [Function.update_apply];split_ifs <;> simp_all
  obtain ⟨b,hb,hbb⟩:=cleanup_executes g (0:Fin 48) (Function.update s 0 []) B hnext
  simp only [Function.update_self] at hb
  refine ⟨(s 0).length+1+b+2,seq_executes _ _ g hc hb,?_⟩
  have hs:=hB 0
  omega

theorem program_executes (g : BitString→ℕ) (raw : BitString) :
    ∃c,program.Executes g (input raw) (input (result raw)) c ∧c ≤ time.eval raw.length := by
  obtain ⟨a,ha,hab⟩:=UnitOrderProgram.program_executes g raw
  have hB:=ready_bound raw (raw.length+a) (ha.stack_bound (initial_bound raw))
  have hflag:UnitOrderProgram.output raw 1=[UnitOrderProgram.accepts raw]:=(UnitOrderProgram.output_fields raw).2.1
  cases hok:UnitOrderProgram.accepts raw with
  | false=>
    obtain ⟨b,hb,hbb⟩:=reject_executes g (ready raw) (raw.length+a) hB
    have hbranch:(branchPop (1:Fin 48) reject reject positive).Executes g (UnitOrderProgram.output raw) (input []) (b+2):=
      branchPop_false 1 _ _ _ g (by rw [hflag,hok]) hb
    rw [rejected raw hok]
    refine ⟨a+(b+2)+2,seq_executes _ _ g ha hbranch,?_⟩
    simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
    omega
  | true=>
    obtain ⟨G,hd,hu⟩:=(UnitOrderProgram.accepts_iff raw).mp hok
    obtain ⟨b,hb,hbb⟩:=positive_executes g raw G hd hu (raw.length+a) hB
    have hbranch:(branchPop (1:Fin 48) reject reject positive).Executes g (UnitOrderProgram.output raw) (input (bytes G)) (b+2):=
      branchPop_true 1 _ _ _ g (by rw [hflag,hok]) hb
    rw [accepted hd hu]
    refine ⟨a+(b+2)+2,seq_executes _ _ g ha hbranch,?_⟩
    have hm:=polynomial_nat_eval_mono computeTime (GraphInput.decode_vertices_bound hd)
    dsimp only at hm
    simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
    omega
lemma program_queryFree : program.QueryFree:=seq_queryFree _ _ UnitOrderProgram.program_queryFree
  (branchPop_queryFree _ _ _ _ hr hr hp) where
  hr:reject.QueryFree:=seq_queryFree _ _ (clear_queryFree _) (cleanup_queryFree _)
  hp:positive.QueryFree:=seq_queryFree _ _ compute_queryFree (cleanResult_queryFree _ _ _ _)

theorem polynomial_graph_to_coordinates : PolyTime result:=
  polyTime_of_block program program_queryFree time (by
    intro raw
    obtain ⟨c,hc,hb⟩:=program_executes (fun _=>0) raw
    exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩)

theorem accepted_roundtrip (raw : BitString) (G : GraphInput) (hd:GraphInput.decode raw=some G)
    (hu:RealUnitInterval.UnitIntervalGraph G.2.graph) : CoordinateGraph.bits (result raw)=G.encode := by
  rw [accepted hd hu]
  exact roundtrip G hu

theorem succeeds_iff (raw : BitString) : result raw≠[] ↔
    ∃G : GraphInput,GraphInput.decode raw=some G ∧RealUnitInterval.UnitIntervalGraph G.2.graph := by
  rw [nonempty_iff,UnitOrderProgram.accepts_iff]
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionRaw
