import HiddenCircuits.Complexity.PairSerialization
import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary
import HiddenCircuits.Complexity.PolynomialBounds
import HiddenCircuits.Complexity.GraphVerifier.GuardSemantics

/-! Actual first-component preprocessing, retaining the original certificate. -/
namespace HiddenCircuits.Complexity.PairPreprocess
open OracleBlock GraphVerifier GraphVerifier.Runtime Polynomial
variable {k : ℕ}

def bankMap : Fin (k+1) ↪ Fin (k+5) where
  toFun i := ⟨i.val+4,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have:=congrArg Fin.val h;dsimp at this;omega

def parseMap : Fin 4 ↪ Fin (k+5) where
  toFun i := if i.val=0 then 0 else if i.val=1 then 4 else if i.val=2 then 1 else 2
  inj' := by intro i j h;have hv:=congrArg Fin.val h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff,-Fin.val_eq_zero_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (show 4<k+5 by omega),Nat.mod_eq_of_lt (show 3<k+5 by omega),Nat.mod_eq_of_lt (show 2<k+5 by omega),Nat.mod_eq_of_lt (show 1<k+5 by omega)]

def pairMap : Fin 3 ↪ Fin (k+5) where
  toFun i := if i.val=0 then 0 else if i.val=1 then 4 else 3
  inj' := by intro i j h;have hv:=congrArg Fin.val h;fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff,-Fin.val_eq_zero_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (show 4<k+5 by omega),Nat.mod_eq_of_lt (show 3<k+5 by omega),Nat.mod_eq_of_lt (show 1<k+5 by omega)]

def working (right left : BitString) : Store (k+4) := fun i =>
  if i.val=0 then right else if i.val=4 then left else []
def parsed (xs : BitString) : Store (k+4) :=
  Function.update (working (parse xs).right (parse xs).left) 2 [(parse xs).ok]

def mapFirst (f : BitString → BitString) (xs : BitString) : BitString :=
  match unpairBits xs with | none => [] | some (x,w) => pairBits (f x) w

noncomputable def cleanRun (B : OracleBlock k) : OracleBlock k := seq B (cleanup 0)
noncomputable def cleanTime (p : Polynomial ℕ) : Polynomial ℕ := p+C (k+1)*(X+p+3)+3
noncomputable def trueBranch (B : OracleBlock k) : OracleBlock (k+4) :=
  seq (rename (cleanRun B) bankMap) (PairSerialization.on pairMap)
noncomputable def program (B : OracleBlock k) : OracleBlock (k+4) :=
  seq (unpairOn parseMap) (branchPop 2 (clear 0) (clear 0) (trueBranch B))
noncomputable def time (p size : Polynomial ℕ) : Polynomial ℕ := 10*X+cleanTime (k:=k) p+10*size+30

theorem cleanRun_executes (B : OracleBlock k) (g : BitString → ℕ) (f : BitString → BitString) (p : Polynomial ℕ)
    (hB : ∀x,∃s c,B.Executes g (Function.update (fun _=>[]) 0 x) s c ∧s 0=f x∧c≤p.eval x.length) (x : BitString) :
    ∃c,(cleanRun B).Executes g (Function.update (fun _=>[]) 0 x) (Function.update (fun _=>[]) 0 (f x)) c ∧
      c≤(cleanTime (k:=k) p).eval x.length := by
  obtain ⟨s,a,ha,ho,hba⟩:=hB x
  obtain ⟨b,hb,hbb⟩:=cleanup_executes g (0:Fin (k+1)) s (x.length+a) (ha.stack_bound (B.machine.init_stack_bound x))
  rw [ho] at hb
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [cleanTime,eval_add,eval_mul,eval_C,eval_X,eval_ofNat]
  nlinarith

theorem parsed_executes (g : BitString → ℕ) (xs : BitString) :
    (unpairOn (parseMap (k:=k))).Executes g (Function.update (fun _=>[]) 0 xs) (parsed xs)
      (parseCost xs+2*(parse xs).left.length+1) := by
  apply unpairOn_executes
  · funext i;fin_cases i <;> simp [parseMap,Function.update_apply,Fin.ext_iff,-Fin.val_eq_zero_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (show 4<k+5 by omega),Nat.mod_eq_of_lt (show 2<k+5 by omega)] <;> rfl
  · funext i;fin_cases i <;> simp [parseMap,parsed,working,Function.update_apply,Fin.ext_iff,-Fin.val_eq_zero_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (show 4<k+5 by omega),Nat.mod_eq_of_lt (show 2<k+5 by omega)] <;> rfl
  · intro i hi
    have h0:i.val≠0 :=by intro h;exact hi 0 (Fin.ext h.symm)
    have h2:i.val≠2 :=by intro h;exact hi 3 (Fin.ext h.symm)
    have h4:i.val≠4 :=by intro h;exact hi 1 (Fin.ext h.symm)
    simp [parsed,working,Function.update_apply,show i≠0 by exact fun h=>h0 (congrArg Fin.val h),
      show i≠2 by exact fun h=>h2 (congrArg Fin.val h),h0,h4]

theorem trueBranch_executes (B : OracleBlock k) (g : BitString → ℕ) (f : BitString → BitString) (p : Polynomial ℕ)
    (hB : ∀x,∃s c,B.Executes g (Function.update (fun _=>[]) 0 x) s c ∧s 0=f x∧c≤p.eval x.length)
    (x w : BitString) :
    ∃c,(trueBranch B).Executes g (working w x) (Function.update (fun _=>[]) 0 (pairBits (f x) w)) c ∧
      c≤(cleanTime (k:=k) p).eval x.length+10*(f x).length+11 := by
  obtain ⟨a,ha,hba⟩:=cleanRun_executes B g f p hB x
  have hc : (rename (cleanRun B) bankMap).Executes g (working w x) (working w (f x)) a := by
    apply rename_executes_to _ bankMap g ha
    · clear ha;funext i;simp [working,bankMap,Function.update_apply,show i.val+4≠0 by omega]

    · clear ha;funext i;simp [working,bankMap,Function.update_apply,show i.val+4≠0 by omega]

    · clear ha;intro i hi
      have h4:i.val≠4 :=by intro h;exact hi 0 (Fin.ext (by simpa [bankMap] using h.symm))
      simp [working,h4]
  have hp := PairSerialization.on_executes (pairMap (k:=k)) g (working w (f x)) (f x) w
    (by funext i;fin_cases i <;> rfl)
  have hout : Function.update (Function.update (working w (f x)) (pairMap 1) []) (pairMap 0) (pairBits (f x) w)=
      Function.update (fun _ : Fin (k+5)=>[]) 0 (pairBits (f x) w) := by
    funext i;simp [pairMap,working,Function.update_apply,Fin.ext_iff,-Fin.val_eq_zero_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (show 4<k+5 by omega)]
    split_ifs <;> rfl
  rw [hout] at hp
  exact ⟨_,seq_executes _ _ g hc hp,by omega⟩

theorem program_executes (B : OracleBlock k) (g : BitString → ℕ) (f : BitString → BitString) (p size : Polynomial ℕ)
    (hB : ∀x,∃s c,B.Executes g (Function.update (fun _=>[]) 0 x) s c ∧s 0=f x∧c≤p.eval x.length)
    (hsize : ∀x,(f x).length≤size.eval x.length) (xs : BitString) :
    ∃s c,(program B).Executes g (Function.update (fun _=>[]) 0 xs) s c ∧
      s 0=mapFirst f xs ∧c≤(time (k:=k) p size).eval xs.length := by
  have hparse:=parsed_executes (k:=k) g xs
  have ht:=unpair_cost_bound xs
  have hl:=parse_lengths xs
  have hpop : Function.update (parsed (k:=k) xs) 2 []=working (parse xs).right (parse xs).left := by
    funext i;simp [parsed,working,Function.update_apply,Fin.ext_iff,-Fin.val_eq_zero_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (show 2<k+5 by omega)];split_ifs <;> simp_all
  cases hok:(parse xs).ok with
  | false =>
    have hc:=clear_executes g (0:Fin (k+5)) (working (parse xs).right (parse xs).left)
    have hb:=branchPop_false (2:Fin (k+5)) (clear 0) (clear 0) (trueBranch B) g
      (s:=parsed xs) (rest:=[]) (by simp [parsed,hok]) (by rw [hpop];exact hc)
    refine ⟨_,_,seq_executes _ _ g hparse hb,?_,?_⟩
    · simp [mapFirst,parse_spec,hok]
    · change _≤(time (k:=k) p size).eval xs.length
      simp only [working,Fin.val_zero,ite_true]
      simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
      omega
  | true =>
    obtain ⟨a,ha,hba⟩:=trueBranch_executes B g f p hB (parse xs).left (parse xs).right
    have hb:=branchPop_true (2:Fin (k+5)) (clear 0) (clear 0) (trueBranch B) g
      (s:=parsed xs) (rest:=[]) (by simp [parsed,hok]) (by rw [hpop];exact ha)
    refine ⟨_,_,seq_executes _ _ g hparse hb,?_,?_⟩
    · simp [mapFirst,parse_spec,hok]
    · have hp:=polynomial_nat_eval_mono (cleanTime (k:=k) p) hl.1
      have hs:=(hsize (parse xs).left).trans (polynomial_nat_eval_mono size hl.1)
      dsimp only at hp hs
      simp only [time,eval_add,eval_mul,eval_ofNat,eval_X]
      omega

lemma program_queryFree (B : OracleBlock k) (hB:B.QueryFree) : (program B).QueryFree :=
  seq_queryFree _ _ (unpairOn_queryFree _) (branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _)
    (seq_queryFree _ _ (rename_queryFree _ _ (seq_queryFree _ _ hB (cleanup_queryFree _))) (PairSerialization.on_queryFree _)))
end HiddenCircuits.Complexity.PairPreprocess
