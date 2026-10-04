import HiddenCircuits.DH.LayerExecution
import HiddenCircuits.DH.LayerInputSemantics
import HiddenCircuits.DH.LayerLiveClosure
import HiddenCircuits.DH.LayerLoopResources

/-! Success and graph semantics of the executable static BFS-layer loops. -/
namespace HiddenCircuits.DH.LayerExecution
open SimpleGraph LexBFSPartition LinearBuckets BlockCollapse LayerSchedule LayerScheduleForest

abbrev Alive {n : ℕ} (s : Working n) : Set (Fin n) := {v | s.store.alive[v.val]=true}
abbrev owner {n : ℕ} (p : LayerInput.Prepared n) (v : Fin n) := p.owners[v.val]
abbrev depth {n : ℕ} (p : LayerInput.Prepared n) (v : Fin n) := p.depths[v.val].val

/-- The live arrays retain the exact original graph partition and BFS relations. -/
structure Good {n : ℕ} (G : SimpleGraph (Fin n)) (p : LayerInput.Prepared n) (s : Working n) : Prop where
  interpretation : Nonempty (ModuleExecution.Interpretation G s.store)
  forest : LiveInvariant G (owner p) (depth p) (Alive s)

def Bounded {n : ℕ} (p : LayerInput.Prepared n) (k : ℕ) (s : Working n) : Prop :=
  ∀v∈Alive s, depth p v≤k

def Independent {n : ℕ} (G : SimpleGraph (Fin n)) (p : LayerInput.Prepared n)
    (k : ℕ) (s : Working n) : Prop :=
  ∀u∈Alive s, ∀v∈Alive s, depth p u=k → depth p v=k → ¬G.Adj u v

lemma Bounded.mono {n : ℕ} {p : LayerInput.Prepared n} {k : ℕ} {s t : Working n}
    (h : Bounded p k s) (hst : Alive t⊆Alive s) : Bounded p k t :=
  fun v hv => h v (hst hv)

lemma Independent.mono {n : ℕ} {G : SimpleGraph (Fin n)} {p : LayerInput.Prepared n}
    {k : ℕ} {s t : Working n} (h : Independent G p k s) (hst : Alive t⊆Alive s) : Independent G p k t :=
  fun u hu v hv => h u (hst hu) v (hst hv)

lemma Good.module_mask {n : ℕ} {G : SimpleGraph (Fin n)} {p : LayerInput.Prepared n} {s t : Working n}
    (hs : Good G p s) (hi : Nonempty (ModuleExecution.Interpretation G t.store))
    (vs : List (Fin n)) (keep : Fin n) (hk : keep∈vs)
    (hlive : ∀v∈vs, v∈Alive s)
    (hm : HiddenCircuits.DH.GraphModule (ModuleExecution.liveGraph G s.store)
      (ModuleExecution.liveModule s.store vs : Set (ModuleExecution.Live s.store)))
    (k : ℕ) (hd : ∀v∈vs, depth p v=k)
    (hroots : ∀v, owner p v=keep ∨ owner p v∉vs)
    (hmask : ∀v, v∈Alive t ↔ v∈Alive s ∧ (v=keep ∨ v∉vs)) : Good G p t := by
  refine ⟨hi,?_⟩
  apply hs.forest.module_mask (ModuleExecution.liveModule s.store vs) ⟨keep,hlive keep hk⟩
    (by simpa using hk) hm k
  · intro v hv; exact hd v.val (by simpa using hv)
  · intro v
    rcases hroots v with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (by simpa using he)
  · intro v
    rw [hmask]
    constructor
    · rintro ⟨ha,he | he⟩
      · exact ⟨ha,Or.inl (Subtype.ext he)⟩
      · exact ⟨ha,Or.inr (by simpa using he)⟩
    · rintro ⟨ha,he | he⟩
      · exact ⟨ha,Or.inl (congrArg Subtype.val he)⟩
      · exact ⟨ha,Or.inr (by simpa using he)⟩

lemma filterLive_mem {n : ℕ} (s : Working n) (vs : List (Fin n)) (v : Fin n) :
    v∈(filterLive s.store vs).value ↔ v∈vs ∧ v∈Alive s := by
  simp only [filterLive_value,List.mem_filter,Alive,Set.mem_setOf_eq]

section Ordinary
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
  (hn : ∀v : Fin n, rows[v.val].Nodup)
local notation "p" => LayerInput.prepare G rows hr hn

/-- Every nonempty farthest component step succeeds, retaining one member;
empty original components are skipped by the literal branch. -/
theorem componentStep_correct (hG : DistanceHereditaryGraph G)
    (k : Fin (n+1)) (hk : 0<k.val) (r : Fin n)
    (hrk : r∈(p).componentByLevel[k.val]) (s : Working n)
    (hs : Good G p s) (hb : Bounded p k.val s) :
    ∃t, (componentStep G rows hr hn p r s).value=some t ∧ Good G p t ∧
      Alive t⊆Alive s ∧
      (∀u∈Alive t, ∀v∈Alive t, u∈(p).components[r.val] → v∈(p).components[r.val] → u=v) ∧
      (componentStep G rows hr hn p r s).accesses+1000*livePotential (p).degree t.store.alive ≤
        1000*livePotential (p).degree s.store.alive+3*((p).components[r.val]).length+4 := by
  let vs := (filterLive s.store (p).components[r.val]).value
  by_cases he : vs=[]
  · refine ⟨s,?_,hs,fun _ h=>h,?_,?_⟩
    · simp only [componentStep,show (filterLive s.store (p).components[r.val]).value=[] from he,↓reduceDIte]
    · intro u hu v hv hur hvr
      have hum : u∈vs := (filterLive_mem s _ u).mpr ⟨hur,hu⟩
      rw [he] at hum
      exact False.elim (List.not_mem_nil hum)
    · have hc := filterLive_accesses s.store (p).components[r.val]
      simp only [componentStep,show (filterLive s.store (p).components[r.val]).value=[] from he,↓reduceDIte]
      omega
  · obtain ⟨u,hu⟩ := List.exists_mem_of_ne_nil vs he
    have hu' := (filterLive_mem s _ u).mp hu
    let C := (sameDepthGraph G (depth p)).connectedComponentMk r
    have hC (v : Fin n) : v∈(p).components[r.val] ↔ v∈C.supp := by
      rw [LayerInput.prepare_component_mem G rows hr hn k r hrk]
      change _ ↔ (sameDepthGraph G (depth p)).connectedComponentMk v=(sameDepthGraph G (depth p)).connectedComponentMk r
      rw [ConnectedComponent.eq]
      exact ⟨Reachable.symm,Reachable.symm⟩
    have hd (v : Fin n) (hv : v∈vs) : depth p v=k.val :=
      congrArg Fin.val (LayerInput.prepare_component_depth G rows hr hn k r hrk v ((filterLive_mem s _ v).mp hv).1)
    have hset : (ModuleExecution.liveModule s.store vs : Set (ModuleExecution.Live s.store))=
        {v:Alive s | v.val∈C.supp} := by
      ext v
      simp only [Finset.mem_coe,ModuleExecution.mem_liveModule,vs,filterLive_mem,Set.mem_setOf_eq]
      exact ⟨fun h=>(hC v.val).mp h.1,fun h=>⟨(hC v.val).mpr h,v.property⟩⟩
    have hm := phaseA_module hG (LayerInput.prepare_rooting G rows hr hn) hs.forest k.val
      (fun v=>hb v.val v.property) C ⟨u,hu'.2⟩ ((hC u).mp hu'.1) (hd u hu)
    rw [←hset] at hm
    obtain ⟨out,ho,hi,hkeep,hmin,hmask⟩ := contractList_correct G rows hr hn (p).degree vs
      (filterLive_nodup s.store _ ((p).component_nodup r)) he s hs.interpretation.some
      (filterLive_live s.store _) hm.1 hm.2
    have hroot (v : Fin n) : owner p v∉vs :=
      roots_survive_positive_module (LayerInput.prepare_rooting G rows hr hn) hk hd v
    have hg := hs.module_mask hi vs out.kept hkeep (filterLive_live s.store _) hm.1 k.val hd
      (fun v=>Or.inr (hroot v)) hmask
    have hstep : (componentStep G rows hr hn p r s).value=some out.state := by
      simp only [componentStep,show (filterLive s.store (p).components[r.val]).value≠[] from he,↓reduceDIte]
      change Option.map Result.state (contractList G rows hr hn (p).degree vs _ s).value=some out.state
      rw [ho];rfl
    obtain ⟨charged,hcharged,hci,hcost⟩ := componentStep_charge G rows hr hn p
      (LayerInput.prepare_degree G rows hr hn) r s hs.interpretation.some
      (fun _=>hm.1) (fun _=>hm.2)
    have heq : charged=out.state := Option.some.inj (hcharged.symm.trans hstep)
    rw [heq] at hcost
    refine ⟨out.state,hstep,hg,fun v hv=>(hmask v).mp hv |>.1,?_,hcost⟩
    · intro a ha b hb' har hbr
      have ha' := (hmask a).mp ha
      have hb' := (hmask b).mp hb'
      have hav : a∈vs := (filterLive_mem s _ a).mpr ⟨har,ha'.1⟩
      have hbv : b∈vs := (filterLive_mem s _ b).mpr ⟨hbr,hb'.1⟩
      exact (ha'.2.resolve_right (not_not.mpr hav)).trans (hb'.2.resolve_right (not_not.mpr hbv)).symm


/-- At a positive independent farthest layer, the original-size-minimum vertex
has a nonempty cograph predecessor module; the actual contraction and pendant
array update therefore both succeed. -/
theorem vertexStep_correct (hG : DistanceHereditaryGraph G)
    (k : ℕ) (hk : 0<k) (u : Fin n) (huk : depth p u=k) (s : Working n)
    (hs : Good G p s) (hb : Bounded p k s) (hind : Independent G p k s)
    (hsize : ∀v∈Alive s, depth p v=k →
      ((p).previous[u.val]).length≤((p).previous[v.val]).length) :
    ∃t, (vertexStep G rows hr hn p u s).value=some t ∧ Good G p t ∧
      Alive t⊆Alive s ∧ u∉Alive t ∧
      (vertexStep G rows hr hn p u s).accesses+1000*livePotential (p).degree t.store.alive ≤
        1000*livePotential (p).degree s.store.alive+3*((p).previous[u.val]).length+4 := by
  have hroot : Rooting G (owner p) (depth p) := LayerInput.prepare_rooting G rows hr hn
  by_cases hu : u∈Alive s
  · let u' : Alive s := ⟨u,hu⟩
    let ru : Alive s := ⟨owner p u,hs.forest.roots_alive u⟩
    let vs := (filterLive s.store (p).previous[u.val]).value
    have hmem (v : Fin n) : v∈vs ↔ v∈forestPredecessors G (depth p) u ∧ v∈Alive s := by
      rw [filterLive_mem,LayerInput.prepare_previous_mem]
    have hset : (ModuleExecution.liveModule s.store vs : Set (ModuleExecution.Live s.store))=
        predecessors (ModuleExecution.liveGraph G s.store) ru u' := by
      ext v
      simp only [Finset.mem_coe,ModuleExecution.mem_liveModule]
      have hv : v∈predecessors (ModuleExecution.liveGraph G s.store) ru u' ↔
          v.val∈forestPredecessors G (depth p) u := live_forest_predecessor_iff hG hroot hs.forest u' v
      rw [hv,hmem]
      exact and_iff_left v.property
    have hru : (ModuleExecution.liveGraph G s.store).Reachable ru u' :=
      (hs.forest.reachable ru u').mpr (hroot.reachable u)
    have hpos : 0<(ModuleExecution.liveGraph G s.store).dist ru u' := by
      have hdist : (ModuleExecution.liveGraph G s.store).dist ru u'=depth p u := live_depth hG hroot hs.forest u'
      rw [hdist,huk];exact hk
    obtain ⟨a,ha⟩ := predecessors_nonempty hru hpos
    have hav : a.val∈vs := by
      have has : a∈ModuleExecution.liveModule s.store vs := by
        change a∈(ModuleExecution.liveModule s.store vs : Set (ModuleExecution.Live s.store))
        rw [hset];exact ha
      simpa using has
    have hne : vs≠[] := by intro he;rw [he] at hav;exact List.not_mem_nil hav
    have hm := phaseB_module hG hroot hs.forest u' (by simpa only [u',huk] using hk) (by
      intro z hz hd
      rw [←LayerInput.prepare_previous_ncard G rows hr hn u,
        ←LayerInput.prepare_previous_ncard G rows hr hn z.val]
      exact hsize z.val z.property (hd.trans huk))
    change GraphModule (ModuleExecution.liveGraph G s.store)
      (predecessors (ModuleExecution.liveGraph G s.store) ru u') ∧
      P4Free ((ModuleExecution.liveGraph G s.store).induce
        (predecessors (ModuleExecution.liveGraph G s.store) ru u')) at hm
    rw [←hset] at hm
    obtain ⟨out,ho,hi,hkeep,hmin,hmask⟩ := contractList_correct G rows hr hn (p).degree vs
      (filterLive_nodup s.store _ ((p).previous_nodup u)) hne s hs.interpretation.some
      (filterLive_live s.store _) hm.1 hm.2
    let keep' : Alive s := ⟨out.kept,(hmem out.kept).mp hkeep |>.2⟩
    have hkeepS : keep'∈ModuleExecution.liveModule s.store vs := by simpa using hkeep
    have hsurv := predecessor_module_survivors_reachable hru hset hkeepS
    have hd (v : Fin n) (hv : v∈vs) : depth p v=k-1 := by
      have hvd := ((hmem v).mp hv).1.2
      rw [huk] at hvd
      omega
    have hroots (v : Fin n) : owner p v=out.kept ∨ owner p v∉vs := by
      by_cases hv : owner p v∈vs
      · left
        have hp := ((hmem (owner p v)).mp hv).1
        have he := hroot.constant (owner p v) u hp.1.reachable
        rw [hroot.root_fixed] at he
        have hrs : ru∈ModuleExecution.liveModule s.store vs := by
          rw [ModuleExecution.mem_liveModule]
          change owner p u∈vs
          rw [←he];exact hv
        exact he.trans (congrArg Subtype.val (hsurv.1.resolve_right (not_not.mpr hrs)))
      · exact Or.inr hv
    have hg := hs.module_mask hi vs out.kept hkeep (filterLive_live s.store _) hm.1 (k-1) hd hroots hmask
    have hunot : u∉vs := by intro hv;exact ((hmem u).mp hv).1.1.ne rfl
    have huout : u∈Alive out.state := (hmask u).mpr ⟨hu,Or.inr hunot⟩
    have hkout : out.kept∈Alive out.state := (hmask out.kept).mpr ⟨(hmem out.kept).mp hkeep |>.2,Or.inl rfl⟩
    have hp : PendantPair (ModuleExecution.liveGraph G out.state.store) ⟨out.kept,hkout⟩ ⟨u,huout⟩ := by
      refine ⟨((hmem out.kept).mp hkeep).1.1.symm,?_⟩
      intro v huv
      have hvold := ((hmask v.val).mp v.property).1
      have hedge : G.Adj u v.val := huv
      have he := hroot.constant u v.val hedge.reachable
      have hvd : G.dist (owner p u) v.val=depth p v.val := by
        rw [hroot.distance v.val,he]
      have hud : G.dist (owner p u) u=k := (hroot.distance u).symm.trans huk
      have hdif := hedge.diff_dist_adj (u:=owner p u)
      rw [hvd,hud] at hdif
      have hle := hb v.val hvold
      have hneq : depth p v.val≠k := fun hh=>hind u hu v.val hvold huk hh hedge
      have hpred : v.val∈forestPredecessors G (depth p) u := ⟨hedge.symm,by rw [huk];omega⟩
      have hvs : v.val∈vs := (hmem v.val).mpr ⟨hpred,hvold⟩
      exact Subtype.ext (((hmask v.val).mp v.property).2.resolve_right (not_not.mpr hvs))
    let t := (absorbWorking out.state out.kept u).value
    have htmask (v : Fin n) : v∈Alive t ↔ v∈Alive out.state ∧ v≠u :=
      ModuleExecution.absorb_alive out.state.store out.kept u v
    have hgood : Good G p t := by
      refine ⟨⟨hi.some.absorb out.kept u hkout huout hp⟩,?_⟩
      apply hg.forest.pendant_mask ⟨out.kept,hkout⟩ ⟨u,huout⟩ hp
      · have hdkeep := hd out.kept hkeep
        change depth p u≠depth p out.kept
        rw [huk,hdkeep];omega
      · exact roots_survive_positive_pendant hroot (by change 0<depth p u;rw [huk];exact hk)
      · exact htmask
    have hstep : (vertexStep G rows hr hn p u s).value=some t := by
      dsimp only [vs] at ho
      simp only [vertexStep,if_pos (show s.store.alive[u.val]=true from hu),ho]
      rfl
    have hnot : u∉(p).previous[u.val] := by
      intro hm
      exact ((LayerInput.prepare_previous_mem G rows hr hn u u).mp hm).1.ne rfl
    obtain ⟨charged,hcharged,hcost⟩ := vertexStep_charge G rows hr hn p
      (LayerInput.prepare_degree G rows hr hn) u s hs.interpretation.some hnot
      (fun _=>hne) (fun _=>hm.1) (fun _=>hm.2)
    have heq : charged=t := Option.some.inj (hcharged.symm.trans hstep)
    rw [heq] at hcost
    refine ⟨t,hstep,hgood,?_,?_,hcost⟩
    · intro v hv; exact ((hmask v).mp ((htmask v).mp hv).1).1
    · intro hv;exact ((htmask u).mp hv).2 rfl
  · refine ⟨s,by simp only [vertexStep,if_neg (show s.store.alive[u.val]≠true from hu)],hs,fun _ h=>h,hu,?_⟩
    simp only [vertexStep,if_neg (show s.store.alive[u.val]≠true from hu)]
    omega


/-- The complete component pass preserves the original graph interpretation and
makes the selected farthest level independent. Each static component is visited
once by the actual list loop. -/
theorem componentPhase_correct (hG : DistanceHereditaryGraph G)
    (k : Fin (n+1)) (hk : 0<k.val) (s : Working n)
    (hs : Good G p s) (hb : Bounded p k.val s) :
    ∃t, (runSteps (componentStep G rows hr hn p) (p).componentByLevel[k.val] s).value=some t ∧
      Good G p t ∧ Bounded p k.val t ∧ Independent G p k.val t ∧
      (runSteps (componentStep G rows hr hn p) (p).componentByLevel[k.val] s).accesses+
        1000*livePotential (p).degree t.store.alive ≤
        1000*livePotential (p).degree s.store.alive+componentBudget p k := by
  let full := (p).componentByLevel[k.val]
  let Unique (r : Fin n) (t : Working n) : Prop :=
    ∀u∈Alive t, ∀v∈Alive t, u∈(p).components[r.val] → v∈(p).components[r.val] → u=v
  let Inv (todo : List (Fin n)) (t : Working n) : Prop :=
    Good G p t ∧ Bounded p k.val t ∧ todo⊆full ∧
      ∀r∈full, r∉todo → Unique r t
  have hstart : Inv full s := ⟨hs,hb,fun _ h=>h,fun _ hr hnot=>False.elim (hnot hr)⟩
  have hstep : ∀r rs t, Inv (r::rs) t → ∃out,
      (componentStep G rows hr hn p r t).value=some out ∧ Inv rs out ∧
      (componentStep G rows hr hn p r t).accesses+1000*livePotential (p).degree out.store.alive ≤
        1000*livePotential (p).degree t.store.alive+(3*((p).components[r.val]).length+4) := by
    intro r rs t ht
    obtain ⟨out,ho,hg,ha,hu,hcost⟩ := componentStep_correct G rows hr hn hG k hk r
      (ht.2.2.1 List.mem_cons_self) t ht.1 ht.2.1
    refine ⟨out,ho,⟨hg,ht.2.1.mono ha,?_,?_⟩,hcost⟩
    · intro v hv;exact ht.2.2.1 (List.mem_cons_of_mem _ hv)
    · intro q hq hnot
      by_cases he : q=r
      · subst q;exact hu
      · have hnot' : q∉r::rs := by simpa only [List.mem_cons,not_or] using And.intro he hnot
        intro a hla b hlb hac hbc
        exact ht.2.2.2 q hq hnot' a (ha hla) b (ha hlb) hac hbc
  obtain ⟨t,ho,hi,hcost⟩ := runSteps_potential (componentStep G rows hr hn p) (p).degree
    (fun r=>3*((p).components[r.val]).length+4) Inv full s hstart hstep
  refine ⟨t,ho,hi.1,hi.2.1,?_,?_⟩
  · intro u hu v hv hdu hdv huv
    obtain ⟨r,hrk,hur⟩ := LayerInput.prepare_component_cover G rows hr hn k u (Fin.ext hdu)
    have hru := (LayerInput.prepare_component_mem G rows hr hn k r hrk u).mp hur
    have huv' : (sameDepthGraph G (depth p)).Adj u v := ⟨huv,hdu.trans hdv.symm⟩
    have hvr := (LayerInput.prepare_component_mem G rows hr hn k r hrk v).mpr (hru.trans huv'.reachable)
    have he := hi.2.2.2 r hrk (by simp) u hu v hv hur hvr
    exact huv.ne he
  · simpa only [componentBudget,Nat.add_assoc,show 4+1=5 by rfl] using hcost

/-- Ascending original predecessor sizes give the current inclusion-minimal
module at each live scheduled vertex, even after all previous deletions. -/
theorem vertexPhase_correct (hG : DistanceHereditaryGraph G)
    (k : Fin (n+1)) (hk : 0<k.val) (s : Working n)
    (hs : Good G p s) (hb : Bounded p k.val s) (hind : Independent G p k.val s) :
    ∃t, (runSteps (vertexStep G rows hr hn p) (p).vertexByLevel[k.val] s).value=some t ∧
      Good G p t ∧ Bounded p (k.val-1) t ∧
      (runSteps (vertexStep G rows hr hn p) (p).vertexByLevel[k.val] s).accesses+
        1000*livePotential (p).degree t.store.alive ≤
        1000*livePotential (p).degree s.store.alive+vertexBudget p k := by
  let Inv (todo : List (Fin n)) (t : Working n) : Prop :=
    Good G p t ∧ Bounded p k.val t ∧ Independent G p k.val t ∧
      todo.Pairwise (fun u v=>((p).previous[u.val]).length≤((p).previous[v.val]).length) ∧
      (∀v∈todo, depth p v=k.val) ∧ (∀v∈Alive t, depth p v=k.val → v∈todo)
  have hbucket := LayerInput.prepare_vertex_bucket G rows hr hn k
  have hstart : Inv (p).vertexByLevel[k.val] s := by
    refine ⟨hs,hb,hind,hbucket.2.2,?_,?_⟩
    · intro v hv;exact congrArg Fin.val ((hbucket.2.1 v).mp hv)
    · intro v hv hd;exact (hbucket.2.1 v).mpr (Fin.ext hd)
  have hstep : ∀u us t, Inv (u::us) t → ∃out,
      (vertexStep G rows hr hn p u t).value=some out ∧ Inv us out ∧
      (vertexStep G rows hr hn p u t).accesses+1000*livePotential (p).degree out.store.alive ≤
        1000*livePotential (p).degree t.store.alive+(3*((p).previous[u.val]).length+4) := by
    intro u us t ht
    have hpair := List.pairwise_cons.mp ht.2.2.2.1
    obtain ⟨out,ho,hg,ha,hu,hcost⟩ := vertexStep_correct G rows hr hn hG k.val hk u
      (ht.2.2.2.2.1 u List.mem_cons_self) t ht.1 ht.2.1 ht.2.2.1 (by
        intro v hv hd
        rcases List.mem_cons.mp (ht.2.2.2.2.2 v hv hd) with he | he
        · subst v;exact le_rfl
        · exact hpair.1 v he)
    refine ⟨out,ho,⟨hg,ht.2.1.mono ha,ht.2.2.1.mono ha,hpair.2,?_,?_⟩,hcost⟩
    · intro v hv;exact ht.2.2.2.2.1 v (List.mem_cons_of_mem _ hv)
    · intro v hv hd
      rcases List.mem_cons.mp (ht.2.2.2.2.2 v (ha hv) hd) with he | he
      · exact False.elim (hu (he ▸ hv))
      · exact he
  obtain ⟨t,ho,hi,hcost⟩ := runSteps_potential (vertexStep G rows hr hn p) (p).degree
    (fun u=>3*((p).previous[u.val]).length+4) Inv (p).vertexByLevel[k.val] s hstart hstep
  refine ⟨t,ho,hi.1,?_,?_⟩
  · intro v hv
    have hle := hi.2.1 v hv
    have hneq : depth p v≠k.val := fun he=>List.not_mem_nil (hi.2.2.2.2.2 v hv he)
    omega
  · simpa only [vertexBudget,Nat.add_assoc,show 4+1=5 by rfl] using hcost


/-- The actual descending loop reaches depth zero and never enters a failure
branch on a semantic distance-hereditary graph. -/
theorem runLevels_correct (hG : DistanceHereditaryGraph G)
    (fuel : ℕ) (hf : fuel≤n) (s : Working n) (hs : Good G p s) (hb : Bounded p fuel s) :
    ∃t, (runLevels G rows hr hn p fuel hf s).value=some t ∧ Good G p t ∧ Bounded p 0 t ∧
      (runLevels G rows hr hn p fuel hf s).accesses+1000*livePotential (p).degree t.store.alive ≤
        1000*livePotential (p).degree s.store.alive+prefixBudget p fuel hf := by
  let Inv := fun k t => Good G p t ∧ Bounded p k t
  have hphase : ∀k (hk : k+1≤n) s, Inv (k+1) s →
      ∃mid out,
        (runSteps (componentStep G rows hr hn p) (p).componentByLevel[k+1] s).value=some mid ∧
        (runSteps (vertexStep G rows hr hn p) (p).vertexByLevel[k+1] mid).value=some out ∧
        Inv k out ∧
        (runSteps (componentStep G rows hr hn p) (p).componentByLevel[k+1] s).accesses+
          (runSteps (vertexStep G rows hr hn p) (p).vertexByLevel[k+1] mid).accesses+
          1000*livePotential (p).degree out.store.alive ≤
            1000*livePotential (p).degree s.store.alive+
              componentBudget p ⟨k+1,by omega⟩+vertexBudget p ⟨k+1,by omega⟩ := by
    intro k hk s hi
    let level : Fin (n+1) := ⟨k+1,by omega⟩
    obtain ⟨mid,hm,hgm,hbm,him,hcm⟩ := componentPhase_correct G rows hr hn hG level (by dsimp [level];omega)
      s hi.1 hi.2
    obtain ⟨out,ho,hgo,hbo,hco⟩ := vertexPhase_correct G rows hr hn hG level (by dsimp [level];omega)
      mid hgm hbm him
    refine ⟨mid,out,hm,ho,⟨hgo,?_⟩,?_⟩
    · simpa only [level,Nat.add_sub_cancel] using hbo
    · dsimp only [level] at hcm hco
      omega
  obtain ⟨t,ho,hi,hcost⟩ := runLevels_potential G rows hr hn p Inv hphase fuel hf s ⟨hs,hb⟩
  exact ⟨t,ho,hi.1,hi.2,hcost⟩

lemma initial_good : Good G p (initial n).value := by
  refine ⟨initial_interpretation G,?_⟩
  have he : Alive (initial n).value=Set.univ := by
    ext v
    simp only [Alive,initial,ModuleExecution.initial,Vector.getElem_replicate,Set.mem_setOf_eq,Set.mem_univ]
  rw [he]
  exact LiveInvariant.initial (owner p) (depth p)

lemma initial_bounded : Bounded p n (initial n).value := by
  intro v hv
  exact Nat.le_of_lt_succ ((p).depths[v.val]).isLt

/-- Once only original depth-zero roots remain, the literal live graph is edgeless. -/
lemma zero_edgeless (s : Working n) (hb : Bounded p 0 s) :
    ∀a b : ModuleExecution.Live s.store, ¬(ModuleExecution.liveGraph G s.store).Adj a b := by
  have hroot : Rooting G (owner p) (depth p) := LayerInput.prepare_rooting G rows hr hn
  have hself (v : ModuleExecution.Live s.store) : owner p v.val=v.val := by
    apply (hroot.reachable v.val).dist_eq_zero_iff.mp
    rw [←hroot.distance]
    exact Nat.eq_zero_of_le_zero (hb v.val v.property)
  intro a b hab
  have he := hroot.constant a.val b.val (show G.Adj a.val b.val from hab).reachable
  rw [hself a,hself b] at he
  exact hab.ne (Subtype.ext he)

/-- Ordinary adjacency-list input, with every schedule and cograph structure
computed internally, succeeds and retains an exact interpretation of G. -/
theorem run_correct (hG : DistanceHereditaryGraph G) :
    ∃t, (run G rows hr hn).value=some t ∧ Good G p t ∧ Bounded p 0 t ∧
      (∀a b : ModuleExecution.Live t.store, ¬(ModuleExecution.liveGraph G t.store).Adj a b) ∧
      (run G rows hr hn).accesses≤2060*G.edgeFinset.card+1105*n+21 := by
  obtain ⟨t,ho,hg,hb,hcost⟩ := runLevels_correct G rows hr hn hG n le_rfl (initial n).value
    (initial_good G rows hr hn) (initial_bounded G rows hr hn)
  exact ⟨t,ho,hg,hb,zero_edgeless G rows hr hn t hb,
    run_accesses_of_potential G rows hr hn t hcost⟩

/-- The executable preprocessing returns an actual graph-isomorphic bag forest,
with a proved linear ordinary graph-access bound and no supplied decomposition. -/
theorem decompose_correct (hG : DistanceHereditaryGraph G) :
    ∃forest, (decompose G rows hr hn).value=some forest ∧ Nonempty (BagForest.graph forest ≃g G) ∧
      (decompose G rows hr hn).accesses≤2060*G.edgeFinset.card+1115*n+22 := by
  obtain ⟨t,ho,hg,hb,he,hcost⟩ := run_correct G rows hr hn hG
  obtain ⟨hout,hcount⟩ := decompose_accesses_of_run G rows hr hn t ho hcost
  exact ⟨(ModuleExecution.finish t.store).value,hout,⟨hg.interpretation.some.finishIso he⟩,hcount⟩

end Ordinary
end HiddenCircuits.DH.LayerExecution
