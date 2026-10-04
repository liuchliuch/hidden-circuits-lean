import HiddenCircuits.Approximation.SamplerRuntime.PartnerEdge
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision

/-! A fixed twenty-stack general matching move: conjugate, test two actual matrix
edges, undo on rejection, and physically clear both saved partner addresses. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerMove
open Complexity Complexity.OracleBlock GraphVerifier.Runtime
variable {n : ℕ}
abbrev unary (n : ℕ) : BitString := List.replicate n true

def partnerPermutation (G : MatrixGraph n) (P : PerfectPartner G.graph) : Equiv.Perm (Fin n) where
  toFun := P.val
  invFun := P.val
  left_inv := P.property.1
  right_inv := P.property.1

def allowed (G : MatrixGraph n) (π : Equiv.Perm (Fin n)) (a b : Fin n) : Bool :=
  G.edge a (PartnerConjugation.candidate π a b a) && G.edge b (PartnerConjugation.candidate π a b b)
def result (G : MatrixGraph n) (π : Equiv.Perm (Fin n)) (a b : Fin n) : Equiv.Perm (Fin n) :=
  if allowed G π a b then PartnerConjugation.candidate π a b else π

def state (n : ℕ) (graph data : BitString) (a b : ℕ) (left right flag : BitString) : Store 19 := fun r =>
  if r.val=0 then unary n else if r.val=1 then graph else if r.val=2 then data else if r.val=3 then unary a
  else if r.val=4 then unary b else if r.val=5 then left else if r.val=6 then right else if r.val=7 then flag else []
def testing (n : ℕ) (graph data : BitString) (a b : ℕ) (left right flag fa fb : BitString) : Store 19 :=
  Function.update (Function.update (state n graph data a b left right flag) 8 fa) 9 fb

def conjugateMap : Fin 12 ↪ Fin 20 where
  toFun i := ![2,3,4,5,6,8,9,10,11,12,13,14] i
  inj' := by decide +kernel
def leftMap : Fin 11 ↪ Fin 20 where
  toFun i := ![0,1,2,3,8,10,11,12,13,14,15] i
  inj' := by decide +kernel
def rightMap : Fin 11 ↪ Fin 20 where
  toFun i := ![0,1,2,4,9,10,11,12,13,14,15] i
  inj' := by decide +kernel
def conjunction : List Bool → Bool
  | [a,b] => a&&b
  | _ => false
noncomputable def candidateBlock : OracleBlock 19 := rename PartnerConjugation.program conjugateMap
noncomputable def undoBlock : OracleBlock 19 := rename PartnerConjugation.undo conjugateMap
noncomputable def checkBlock : OracleBlock 19 := seq (rename PartnerEdge.program leftMap)
  (seq (rename PartnerEdge.program rightMap) (decision 7 [8,9] conjunction))
noncomputable def chooseBlock : OracleBlock 19 := branchPop 7 undoBlock undoBlock skip
noncomputable def program : OracleBlock 19 := seq candidateBlock
  (seq checkBlock (seq chooseBlock (seq (clear 5) (clear 6))))

lemma candidate_executes (g : BitString → ℕ) (graph : BitString) (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    ∃t,candidateBlock.Executes g (state n graph (Output.witness π) a.val b.val [] [] [])
      (state n graph (Output.witness (PartnerConjugation.candidate π a b)) a.val b.val (unary (π a).val) (unary (π b).val) []) t ∧
      t≤100000*(n+1)^4 := by
  obtain ⟨t,ht,hb⟩ := PartnerConjugation.program_executes g π a b
  refine ⟨t,?_,hb⟩
  apply rename_executes_to PartnerConjugation.program conjugateMap g ht
  · funext r;fin_cases r <;> rfl
  · funext r;fin_cases r <;> rfl
  · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 3 rfl) | exact False.elim (hr 4 rfl)

lemma check_executes (g : BitString → ℕ) (G : MatrixGraph n) (π : Equiv.Perm (Fin n)) (a b : Fin n) (left right : BitString) :
    ∃t,checkBlock.Executes g (state n G.bits (Output.witness π) a.val b.val left right [])
      (state n G.bits (Output.witness π) a.val b.val left right [G.edge a (π a)&&G.edge b (π b)]) t ∧
      t≤20000*(n+1)^4+12 := by
  let D := Output.witness π
  let fa := G.edge a (π a)
  let fb := G.edge b (π b)
  obtain ⟨c1,h1,b1⟩ := PartnerEdge.program_executes g G π a
  have ha : (rename PartnerEdge.program leftMap).Executes g (state n G.bits D a.val b.val left right [])
      (testing n G.bits D a.val b.val left right [] [fa] []) c1 := by
    apply rename_executes_to PartnerEdge.program leftMap g h1
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 4 rfl)
  obtain ⟨c2,h2,b2⟩ := PartnerEdge.program_executes g G π b
  have hb : (rename PartnerEdge.program rightMap).Executes g (testing n G.bits D a.val b.val left right [] [fa] [])
      (testing n G.bits D a.val b.val left right [] [fa] [fb]) c2 := by
    apply rename_executes_to PartnerEdge.program rightMap g h2
    · funext r;fin_cases r <;> rfl
    · funext r;fin_cases r <;> rfl
    · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 4 rfl)
  have hc : (decision (7:Fin 20) [8,9] conjunction).Executes g (testing n G.bits D a.val b.val left right [] [fa] [fb])
      (state n G.bits D a.val b.val left right [fa&&fb]) 8 := by
    let bits : Fin 20 → Bool := fun r => if r.val=8 then fa else fb
    have hd := decision_executes (7:Fin 20) [8,9] (by decide) (by decide) conjunction bits g
      (testing n G.bits D a.val b.val left right [] [fa] [fb])
      (by intro r hr;fin_cases r <;> simp_all [testing,state,bits])
    convert hd using 1
    funext r;fin_cases r <;> simp [testing,state,eraseStore,conjunction,bits]
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb hc),by omega⟩

lemma flag_pop (n : ℕ) (graph data : BitString) (a b : ℕ) (left right : BitString) (flag : Bool) :
    Function.update (state n graph data a b left right [flag]) 7 []=state n graph data a b left right [] := by
  funext r;fin_cases r <;> rfl

lemma choose_executes (g : BitString → ℕ) (G : MatrixGraph n) (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    ∃t,chooseBlock.Executes g (state n G.bits (Output.witness (PartnerConjugation.candidate π a b)) a.val b.val
      (unary (π a).val) (unary (π b).val) [allowed G π a b])
      (state n G.bits (Output.witness (result G π a b)) a.val b.val (unary (π a).val) (unary (π b).val) []) t ∧
      t≤20000*(n+1)^4+4 := by
  by_cases h : allowed G π a b=true
  · rw [h]
    refine ⟨3,?_,by omega⟩
    have hb := branchPop_true (7:Fin 20) undoBlock undoBlock skip g
      (s:=state n G.bits (Output.witness (PartnerConjugation.candidate π a b)) a.val b.val (unary (π a).val) (unary (π b).val) [true]) rfl
      (by rw [flag_pop];exact skip_executes g _)
    simpa only [result,h,ite_true] using hb
  · have hf : allowed G π a b=false := Bool.eq_false_iff.mpr h
    rw [hf]
    obtain ⟨c,hc,hb⟩ := PartnerConjugation.undo_executes g π a b
    have hu : undoBlock.Executes g (state n G.bits (Output.witness (PartnerConjugation.candidate π a b)) a.val b.val
        (unary (π a).val) (unary (π b).val) [])
        (state n G.bits (Output.witness π) a.val b.val (unary (π a).val) (unary (π b).val) []) c := by
      apply rename_executes_to PartnerConjugation.undo conjugateMap g hc
      · funext r;fin_cases r <;> rfl
      · funext r;fin_cases r <;> rfl
      · intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl)
    refine ⟨c+2,?_,by omega⟩
    have hx := branchPop_false (7:Fin 20) undoBlock undoBlock skip g
      (s:=state n G.bits (Output.witness (PartnerConjugation.candidate π a b)) a.val b.val (unary (π a).val) (unary (π b).val) [false]) rfl
      (by rw [flag_pop];exact hu)
    simpa only [result,hf,ite_false] using hx

theorem program_executes (g : BitString → ℕ) (G : MatrixGraph n) (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    ∃t,program.Executes g (state n G.bits (Output.witness π) a.val b.val [] [] [])
      (state n G.bits (Output.witness (result G π a b)) a.val b.val [] [] []) t ∧
      t≤3000000*(n+1)^4 := by
  obtain ⟨c1,h1,b1⟩ := candidate_executes g G.bits π a b
  obtain ⟨c2,h2,b2⟩ := check_executes g G (PartnerConjugation.candidate π a b) a b (unary (π a).val) (unary (π b).val)
  obtain ⟨c3,h3,b3⟩ := choose_executes g G π a b
  have h4 : (clear (5:Fin 20)).Executes g
      (state n G.bits (Output.witness (result G π a b)) a.val b.val (unary (π a).val) (unary (π b).val) [])
      (state n G.bits (Output.witness (result G π a b)) a.val b.val [] (unary (π b).val) []) ((π a).val+1) := by
    convert clear_executes g (5:Fin 20) _ using 1
    · funext r;fin_cases r <;> rfl
    · simp [state]
  have h5 : (clear (6:Fin 20)).Executes g
      (state n G.bits (Output.witness (result G π a b)) a.val b.val [] (unary (π b).val) [])
      (state n G.bits (Output.witness (result G π a b)) a.val b.val [] [] []) ((π b).val+1) := by
    convert clear_executes g (6:Fin 20) _ using 1
    · funext r;fin_cases r <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 (seq_executes _ _ g h4 h5))),?_⟩
  have ha := (π a).isLt
  have hb := (π b).isLt
  have hp : n+1≤(n+1)^4 := le_self_pow (by omega) (by decide)
  nlinarith

lemma result_partner (G : MatrixGraph n) (P : PerfectPartner G.graph) (a b : Fin n) :
    result G (partnerPermutation G P) a b=partnerPermutation G (QuasimonotoneProof.PartnerSwitch.switch G.graph a b P) := by
  have hc (x : Fin n) : PartnerConjugation.candidate (partnerPermutation G P) a b x=
      QuasimonotoneProof.PartnerSwitch.conjugate a b P.val x :=
    PartnerConjugation.candidate_apply _ P.property.1 a b x
  have he : allowed G (partnerPermutation G P) a b=true ↔
      ∀x,G.graph.Adj x (QuasimonotoneProof.PartnerSwitch.conjugate a b P.val x) := by
    rw [PartnerEdge.conjugate_valid_iff]
    simp only [allowed,Bool.and_eq_true,hc,MatrixGraph.graph]
  apply Equiv.ext
  intro x
  by_cases h : allowed G (partnerPermutation G P) a b=true
  · have hv := he.mp h
    rw [result,if_pos h]
    change PartnerConjugation.candidate (partnerPermutation G P) a b x=
      (QuasimonotoneProof.PartnerSwitch.switch G.graph a b P).val x
    rw [QuasimonotoneProof.PartnerSwitch.switch,dif_pos hv]
    exact hc x
  · have hv := mt he.mpr h
    rw [result,if_neg h]
    change P.val x=(QuasimonotoneProof.PartnerSwitch.switch G.graph a b P).val x
    rw [QuasimonotoneProof.PartnerSwitch.switch,dif_neg hv]

lemma candidateBlock_queryFree : candidateBlock.QueryFree := rename_queryFree _ _ PartnerConjugation.program_queryFree
lemma undoBlock_queryFree : undoBlock.QueryFree := rename_queryFree _ _ PartnerConjugation.undo_queryFree
lemma checkBlock_queryFree : checkBlock.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ PartnerEdge.program_queryFree)
  (seq_queryFree _ _ (rename_queryFree _ _ PartnerEdge.program_queryFree) (decision_queryFree _ _ _))
lemma chooseBlock_queryFree : chooseBlock.QueryFree := branchPop_queryFree _ _ _ _ undoBlock_queryFree undoBlock_queryFree skip_queryFree
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ candidateBlock_queryFree
  (seq_queryFree _ _ checkBlock_queryFree (seq_queryFree _ _ chooseBlock_queryFree (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))

end HiddenCircuits.Approximation.SamplerRuntime.PartnerMove
