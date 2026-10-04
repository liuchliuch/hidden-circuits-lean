import HiddenCircuits.DH.Runtime.UnaryLinear
import HiddenCircuits.DH.Runtime.UniformCoefficientModel
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength

/-! A literal unary test for the rectangular matching
summand indices. Kind is one of three fixed program variants, later selected
by the actual pruning result. -/
namespace HiddenCircuits.DH.Runtime.CoefficientTermIndex
open Complexity Complexity.OracleBlock PruningModel
set_option maxHeartbeats 1200000

def state (i j r k : ℕ) (flag : BitString) (a b : ℕ) : Store 9:=fun q=>
  if q.val=0 then List.replicate i true else if q.val=1 then List.replicate j true
  else if q.val=2 then List.replicate r true else if q.val=3 then List.replicate k true
  else if q.val=4 then flag else if q.val=5 then List.replicate a true
  else if q.val=6 then List.replicate b true else []
def store (i j r k : ℕ) (flag : BitString) : Store 9:=state i j r k flag 0 0
def lhs : Kind→ List (Fin 10) | .twin _=>[0,1] | .pendant=>[0]
def rhs : Kind→ List (Fin 10) | .twin false=>[3] | .twin true=>[3,2,2] | .pendant=>[3,1]
def leftValue : Kind→ ℕ→ ℕ→ ℕ | .twin _,i,j=>i+j | .pendant,i,_=>i
def rightValue : Kind→ ℕ→ ℕ→ ℕ→ ℕ | .twin false,_,_,k=>k | .twin true,_,r,k=>k+2*r | .pendant,j,_,k=>k+j
lemma lhs_ports (kind : Kind) : ∀q∈lhs kind,q≠5 ∧ q≠9:=by cases kind with
  | twin b=>simp [lhs]
  | pendant=>simp [lhs]
lemma rhs_ports (kind : Kind) : ∀q∈rhs kind,q≠6 ∧ q≠9:=by cases kind with
  | twin b=>cases b <;> simp [rhs] <;> decide
  | pendant=>simp [rhs]
noncomputable def makeLeft (kind : Kind) : OracleBlock 9:=UnaryLinear.program 5 9 (lhs kind) (lhs_ports kind) (by decide)
noncomputable def makeRight (kind : Kind) : OracleBlock 9:=UnaryLinear.program 6 9 (rhs kind) (rhs_ports kind) (by decide)
def compareMap : Fin 6↪Fin 10:=⟨fun q=>![5,6,4,7,8,9] q,by decide +kernel⟩
noncomputable def compare : OracleBlock 9:=GraphVerifier.Runtime.readLengthOn compareMap
noncomputable def sumTest (kind : Kind) : OracleBlock 9:=seq (makeLeft kind) (seq (makeRight kind)
  (seq compare (seq (clear 5) (clear 6))))

lemma makeLeft_executes (g : BitString→ ℕ) (kind : Kind) (i j r k : ℕ) :
    ∃t,(makeLeft kind).Executes g (store i j r k []) (state i j r k [] (leftValue kind i j) 0) t ∧
      t≤ 5*(i+j)+9 := by
  let values:Fin 10→ ℕ:=![i,j,r,k,0,0,0,0,0,0]
  have hv:∀q∈lhs kind,store i j r k [] q=List.replicate (values q) true:=by
    cases kind with
    | twin b=>intro q hq;simp only [lhs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq;rcases hq with rfl|rfl <;> rfl
    | pendant=>intro q hq;simp only [lhs,List.mem_singleton] at hq;subst q;rfl
  have h:=UnaryLinear.executes g (5:Fin 10) 9 (lhs kind) (lhs_ports kind) (by decide)
    (store i j r k []) values hv rfl 0 rfl
  refine ⟨5*((lhs kind).map values).sum+4*(lhs kind).length+1,?_,?_⟩
  · convert h using 1
    cases kind with
    | twin b=>funext q;fin_cases q <;> simp [store,state,lhs,leftValue,values]
    | pendant=>funext q;fin_cases q <;> simp [store,state,lhs,leftValue,values]
  · cases kind <;> simp [lhs,values] <;> omega
lemma makeRight_executes (g : BitString→ ℕ) (kind : Kind) (i j r k : ℕ) :
    ∃t,(makeRight kind).Executes g (state i j r k [] (leftValue kind i j) 0)
      (state i j r k [] (leftValue kind i j) (rightValue kind j r k)) t ∧ t≤ 5*(k+2*r+j)+13 := by
  let values:Fin 10→ ℕ:=![i,j,r,k,0,leftValue kind i j,0,0,0,0]
  have hv:∀q∈rhs kind,state i j r k [] (leftValue kind i j) 0 q=List.replicate (values q) true:=by
    cases kind with
    | twin b=>
      cases b with
      | false=>intro q hq;simp only [rhs,List.mem_singleton] at hq;subst q;rfl
      | true=>
        intro q hq
        simp only [rhs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_self] at hq
        rcases hq with rfl|rfl <;> rfl
    | pendant=>intro q hq;simp only [rhs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq;rcases hq with rfl|rfl <;> rfl
  have h:=UnaryLinear.executes g (6:Fin 10) 9 (rhs kind) (rhs_ports kind) (by decide)
    (state i j r k [] (leftValue kind i j) 0) values hv rfl 0 rfl
  refine ⟨5*((rhs kind).map values).sum+4*(rhs kind).length+1,?_,?_⟩
  · convert h using 1
    cases kind with
    | twin b=>cases b <;> funext q <;> fin_cases q <;> simp [state,rhs,leftValue,rightValue,values, Nat.two_mul,Nat.add_assoc]
    | pendant=>funext q;fin_cases q <;> simp [state,rhs,leftValue,rightValue,values]
  · cases kind with
    | twin b=>cases b <;> simp [rhs,values] <;> omega
    | pendant=>simp [rhs,values];omega

lemma sumTest_executes (g : BitString→ ℕ) (kind : Kind) (i j r k : ℕ) :
    ∃t,(sumTest kind).Executes g (store i j r k [])
      (store i j r k [decide (leftValue kind i j=rightValue kind j r k)]) t ∧
      t≤ 50*(i+j+r+k+1)+50 := by
  obtain ⟨a,ha,hab⟩:=makeLeft_executes g kind i j r k
  obtain ⟨b,hb,hbb⟩:=makeRight_executes g kind i j r k
  obtain ⟨c,hc,hcb⟩:=GraphVerifier.Runtime.readLengthOn_executes compareMap g
    (state i j r k [] (leftValue kind i j) (rightValue kind j r k))
    (List.replicate (leftValue kind i j) true) (List.replicate (rightValue kind j r k) true) (by
      funext q;fin_cases q <;> rfl)
  simp only [List.length_replicate] at hc hcb
  let out:=[decide (leftValue kind i j=rightValue kind j r k)]
  have hc':compare.Executes g (state i j r k [] (leftValue kind i j) (rightValue kind j r k))
      (state i j r k out (leftValue kind i j) (rightValue kind j r k)) c:=by
    convert hc using 1
    funext q;fin_cases q <;> rfl
  have hd:(clear (5:Fin 10)).Executes g (state i j r k out (leftValue kind i j) (rightValue kind j r k))
      (state i j r k out 0 (rightValue kind j r k)) (leftValue kind i j+1):=by
    convert clear_executes g (5:Fin 10) (state i j r k out (leftValue kind i j) (rightValue kind j r k)) using 1
    · funext q;fin_cases q <;> rfl
    · simp [state]
  have he:(clear (6:Fin 10)).Executes g (state i j r k out 0 (rightValue kind j r k))
      (store i j r k out) (rightValue kind j r k+1):=by
    convert clear_executes g (6:Fin 10) (state i j r k out 0 (rightValue kind j r k)) using 1
    · funext q;fin_cases q <;> rfl
    · simp [state]
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc' (seq_executes _ _ g hd he))),?_⟩
  cases kind with
  | twin bb=>cases bb <;> simp only [leftValue,rightValue] at * <;> omega
  | pendant=>simp only [leftValue,rightValue] at *;omega

def prePredicate : Kind→ ℕ→ ℕ→ Prop | .twin false,j,r=>r=0 | .twin true,_,_=>True | .pendant,j,r=>r=j
instance (kind : Kind) (j r : ℕ) : Decidable (prePredicate kind j r) := by cases kind with
  | twin b=>cases b <;> unfold prePredicate <;> infer_instance
  | pendant=>unfold prePredicate;infer_instance
def preMap (pendant : Bool) : Fin 6↪Fin 10 where
  toFun q:=![2,(if pendant then 1 else 5),4,7,8,9] q
  inj':=by cases pendant <;> decide +kernel
noncomputable def precheck : Kind→ OracleBlock 9
  | .twin true=>push 4 true
  | .twin false=>GraphVerifier.Runtime.readLengthOn (preMap false)
  | .pendant=>GraphVerifier.Runtime.readLengthOn (preMap true)
noncomputable def program (kind : Kind) : OracleBlock 9:=seq (precheck kind)
  (branchPop 4 (push 4 false) (push 4 false) (sumTest kind))
lemma precheck_executes (g : BitString→ ℕ) (kind : Kind) (i j r k : ℕ) :
    ∃t,(precheck kind).Executes g (store i j r k [])
      (store i j r k [decide (prePredicate kind j r)]) t ∧ t≤ 13*(j+r)+23 := by
  cases kind with
  | twin bb=>cases bb with
    | false=>
      obtain ⟨t,ht,hb⟩:=GraphVerifier.Runtime.readLengthOn_executes (preMap false) g (store i j r k [])
        (List.replicate r true) [] (by funext q;fin_cases q <;> rfl)
      refine ⟨t,?_,by simp only [List.length_replicate,List.length_nil] at hb;omega⟩
      convert ht using 1
      funext q;fin_cases q <;> simp [prePredicate,preMap,store,state]
    | true=>
      refine ⟨1,?_,by omega⟩
      convert push_executes g (4:Fin 10) true (store i j r k []) using 1
      funext q;fin_cases q <;> rfl
  | pendant=>
    obtain ⟨t,ht,hb⟩:=GraphVerifier.Runtime.readLengthOn_executes (preMap true) g (store i j r k [])
      (List.replicate r true) (List.replicate j true) (by funext q;fin_cases q <;> rfl)
    refine ⟨t,?_,by simp only [List.length_replicate] at hb;omega⟩
    convert ht using 1
    funext q;fin_cases q <;> simp [prePredicate,preMap,store,state]
lemma pop_flag (i j r k : ℕ) (b : Bool) : Function.update (store i j r k [b]) 4 []=store i j r k []:=by
  funext q;fin_cases q <;> rfl
lemma test_iff (kind : Kind) (i j r k : ℕ) : UniformCoefficientModel.test kind i j r k ↔
    prePredicate kind j r ∧ leftValue kind i j=rightValue kind j r k := by
  cases kind with
  | twin bb=>cases bb <;> simp [UniformCoefficientModel.test,prePredicate,leftValue,rightValue]
  | pendant=>rfl

theorem executes (g : BitString→ ℕ) (kind : Kind) (i j r k : ℕ) :
    ∃t,(program kind).Executes g (store i j r k [])
      (store i j r k [decide (UniformCoefficientModel.test kind i j r k)]) t ∧
      t≤ 100*(i+j+r+k+1)+100 := by
  obtain ⟨c,hc,hcb⟩:=precheck_executes g kind i j r k
  by_cases hp:prePredicate kind j r
  · simp only [hp,decide_true] at hc
    obtain ⟨t,ht,htb⟩:=sumTest_executes g kind i j r k
    have hb:(branchPop (4:Fin 10) (push 4 false) (push 4 false) (sumTest kind)).Executes g
        (store i j r k [true]) (store i j r k [decide (leftValue kind i j=rightValue kind j r k)]) (t+2):=by
      apply branchPop_true _ _ _ _ g rfl
      rw [pop_flag];exact ht
    have he:decide (UniformCoefficientModel.test kind i j r k)=decide (leftValue kind i j=rightValue kind j r k):=by
      simp [test_iff,hp]
    rw [he]
    exact ⟨_,seq_executes _ _ g hc hb,by omega⟩
  · simp only [hp,decide_false] at hc
    have hb:(branchPop (4:Fin 10) (push 4 false) (push 4 false) (sumTest kind)).Executes g
        (store i j r k [false]) (store i j r k [false]) 3:=by
      apply branchPop_false _ _ _ _ g rfl
      rw [pop_flag]
      convert push_executes g (4:Fin 10) false (store i j r k []) using 1
      funext q;fin_cases q <;> rfl
    have he:¬UniformCoefficientModel.test kind i j r k:=by rw [test_iff];exact fun h=>hp h.1
    simp only [he,decide_false]
    exact ⟨_,seq_executes _ _ g hc hb,by omega⟩
lemma sumTest_queryFree (kind : Kind) : (sumTest kind).QueryFree:=seq_queryFree _ _ (UnaryLinear.queryFree _ _ _ _ _)
  (seq_queryFree _ _ (UnaryLinear.queryFree _ _ _ _ _) (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))
lemma precheck_queryFree (kind : Kind) : (precheck kind).QueryFree:=by
  cases kind with
  | twin bb=>
    cases bb with
    | false=>exact GraphVerifier.Runtime.readLengthOn_queryFree _
    | true=>exact push_queryFree _ _
  | pendant=>exact GraphVerifier.Runtime.readLengthOn_queryFree _
lemma queryFree (kind : Kind) : (program kind).QueryFree:=seq_queryFree _ _ (precheck_queryFree kind)
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (sumTest_queryFree kind))
noncomputable def on {l : ℕ} (φ : Fin 10↪Fin (l+1)) (kind : Kind) : OracleBlock l:=rename (program kind) φ
lemma on_executes {l : ℕ} (φ : Fin 10↪Fin (l+1)) (g : BitString→ ℕ) (s : Store l)
    (kind : Kind) (i j r k : ℕ) (hs:s∘φ=store i j r k []) :
    ∃t,(on φ kind).Executes g s (Function.update s (φ 4) [decide (UniformCoefficientModel.test kind i j r k)]) t ∧
      t≤ 100*(i+j+r+k+1)+100 := by
  obtain ⟨t,ht,hb⟩:=executes g kind i j r k
  refine ⟨t,?_,hb⟩
  apply rename_executes_to _ φ g ht hs
  · have he:(Function.update s (φ 4) [decide (UniformCoefficientModel.test kind i j r k)])∘φ=
        Function.update (s∘φ) 4 [decide (UniformCoefficientModel.test kind i j r k)]:=by
      funext q;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext q;fin_cases q <;> rfl
  · intro q hq;exact Function.update_of_ne (hq 4).symm _ _
lemma on_queryFree {l : ℕ} (φ : Fin 10↪Fin (l+1)) (kind : Kind) : (on φ kind).QueryFree:=
  rename_queryFree _ _ (queryFree kind)
end HiddenCircuits.DH.Runtime.CoefficientTermIndex
