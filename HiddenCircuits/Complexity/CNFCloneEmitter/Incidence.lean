import HiddenCircuits.Complexity.CNFCloneEmitter.LiteralMembership
import HiddenCircuits.Complexity.CNFCloneEmitter.LiteralWord

/-! Actual read-only CNF incidence lookup from canonical clause bytes and unary
variable/clause indices. This is the nontrivial cross-part clone-graph edge test. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter.Incidence
open OracleBlock

/-- Local ports0..7 are the membership parser. Masters8/9/10 are the clause
payload, variable and clause indices. Ports11/12 are lookup work. Output is2. -/
def state (stream word output parsed temporary flag copy work payload varIndex clause input clock : BitString) : Store 12 := fun i =>
  if i.val=0 then stream else if i.val=1 then word else if i.val=2 then output else if i.val=3 then parsed
  else if i.val=4 then temporary else if i.val=5 then flag else if i.val=6 then copy else if i.val=7 then work
  else if i.val=8 then payload else if i.val=9 then varIndex else if i.val=10 then clause else if i.val=11 then input else clock

def wordEmbedding : Fin 4 ↪ Fin 13 where
  toFun i := if i.val=0 then 9 else if i.val=1 then 12 else if i.val=2 then 7 else 1
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def lookupEmbedding : Fin 5 ↪ Fin 13 where
  toFun i := if i.val=0 then 11 else if i.val=1 then 12 else if i.val=2 then 0 else if i.val=3 then 4 else 5
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def memberEmbedding : Fin 8 ↪ Fin 13 := Fin.castAddEmb 5

noncomputable def wordBlock (sign : Bool) : OracleBlock 12 := rename (LiteralWord.program sign) wordEmbedding
noncomputable def lookupBlock : OracleBlock 12 := rename ClauseLookup.program lookupEmbedding
noncomputable def memberBlock : OracleBlock 12 := rename LiteralMembership.program memberEmbedding
noncomputable def program (sign : Bool) : OracleBlock 12 :=
  seq (wordBlock sign) (seq (copyOn 8 11 7 (by decide) (by decide) (by decide))
    (seq (copyOn 10 12 7 (by decide) (by decide) (by decide))
      (seq lookupBlock (seq (push 2 false) (seq memberBlock (clear 1))))))

lemma literalBits_injective {n : ℕ} : Function.Injective (CNF.literalBits (n:=n)) := by
  intro a b h
  have he := congrArg (CNF.decodeLiteral n) h
  simpa only [CNF.decodeLiteral_literalBits,Option.some.injEq] using he

lemma literal_mem_iff {n : ℕ} (l : Fin n × Bool) (ls : List (Fin n × Bool)) :
    CNF.literalBits l∈ls.map CNF.literalBits ↔ l∈ls := by
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := List.mem_map.mp h
    exact literalBits_injective he ▸ ha
  · intro h;exact List.mem_map.mpr ⟨l,h,rfl⟩

lemma member_length_le (w : BitString) (ws : List BitString) (hw : w∈ws) :
    w.length≤(encodeBitList ws).length := by
  induction ws with
  | nil => simp at hw
  | cons a as ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · simp [encodeBitList];omega
    · exact (ih hw).trans (ClauseLookup.encode_tail_length a as)

/-- Real literal incidence execution, with every master restored and all local
work cleared. Its bound depends only on the literal serialized inputs. -/
theorem program_executes {n m : ℕ} (g : BitString → ℕ) (F : CNF n m)
    (i : Fin n) (j : Fin m) (sign : Bool) :
    let payload := encodeBitList ((List.ofFn F.clause).map CNF.clauseBits)
    ∃ cost, (program sign).Executes g
      (state [] [] [] [] [] [] [] [] payload (List.replicate i.val true) (List.replicate j.val true) [] [])
      (state [] [] [decide ((i,sign)∈F.clause j)] [] [] [] [] [] payload
        (List.replicate i.val true) (List.replicate j.val true) [] []) cost ∧
      cost≤500*(payload.length+i.val+j.val+1)^2 := by
  dsimp only
  let payload := encodeBitList ((List.ofFn F.clause).map CNF.clauseBits)
  let target := CNF.literalBits (i,sign)
  let iv := List.replicate i.val true
  let jv := List.replicate j.val true
  have hw : (wordBlock sign).Executes g
      (state [] [] [] [] [] [] [] [] payload iv jv [] [])
      (state [] target [] [] [] [] [] [] payload iv jv [] []) (14*i.val+14) := by
    apply rename_executes_to _ wordEmbedding g (LiteralWord.program_executes g i.val sign)
    · funext k;fin_cases k <;> rfl
    · funext k;fin_cases k <;> rfl
    · intro k hk;fin_cases k <;> first | rfl | exact (hk 0 rfl).elim | exact (hk 1 rfl).elim | exact (hk 2 rfl).elim | exact (hk 3 rfl).elim
  have hp : (copyOn (8 : Fin 13) 11 7 (by decide) (by decide) (by decide)).Executes g
      (state [] target [] [] [] [] [] [] payload iv jv [] [])
      (state [] target [] [] [] [] [] [] payload iv jv payload []) (5*payload.length+2) := by
    convert copyOn_executes g (8 : Fin 13) 11 7 (by decide) (by decide) (by decide)
      (state [] target [] [] [] [] [] [] payload iv jv [] []) rfl using 1
    funext k;fin_cases k <;> simp [state]
  have hi : (copyOn (10 : Fin 13) 12 7 (by decide) (by decide) (by decide)).Executes g
      (state [] target [] [] [] [] [] [] payload iv jv payload [])
      (state [] target [] [] [] [] [] [] payload iv jv payload jv) (5*j.val+2) := by
    convert copyOn_executes g (10 : Fin 13) 12 7 (by decide) (by decide) (by decide)
      (state [] target [] [] [] [] [] [] payload iv jv payload []) rfl using 1
    · funext k;fin_cases k <;> simp [state]
    · simp [state,jv]
  obtain ⟨cl,hl,hbl⟩ := ClauseLookup.program_executes g ((List.ofFn F.clause).map CNF.clauseBits) j.val
  have hget : (((List.ofFn F.clause).map CNF.clauseBits)[j.val]?.getD [])=CNF.clauseBits (F.clause j) := by simp
  rw [hget] at hl
  have hlookup : lookupBlock.Executes g
      (state [] target [] [] [] [] [] [] payload iv jv payload jv)
      (state (CNF.clauseBits (F.clause j)) target [] [] [] [] [] [] payload iv jv [] []) cl := by
    apply rename_executes_to _ lookupEmbedding g hl
    · funext k;fin_cases k <;> rfl
    · funext k;fin_cases k <;> rfl
    · intro k hk;fin_cases k <;> first | rfl | exact (hk 0 rfl).elim | exact (hk 1 rfl).elim | exact (hk 2 rfl).elim | exact (hk 3 rfl).elim | exact (hk 4 rfl).elim
  have hpush : (push (2 : Fin 13) false).Executes g
      (state (CNF.clauseBits (F.clause j)) target [] [] [] [] [] [] payload iv jv [] [])
      (state (CNF.clauseBits (F.clause j)) target [false] [] [] [] [] [] payload iv jv [] []) 1 := by
    convert push_executes g (2 : Fin 13) false
      (state (CNF.clauseBits (F.clause j)) target [] [] [] [] [] [] payload iv jv [] []) using 1
    funext k;fin_cases k <;> rfl
  obtain ⟨cm,hm,hbm⟩ := LiteralMembership.program_executes g ((F.clause j).map CNF.literalBits) target
  have hmem : memberBlock.Executes g
      (state (CNF.clauseBits (F.clause j)) target [false] [] [] [] [] [] payload iv jv [] [])
      (state [] target [decide ((i,sign)∈F.clause j)] [] [] [] [] [] payload iv jv [] []) cm := by
    have he : (target∈(F.clause j).map CNF.literalBits) ↔ (i,sign)∈F.clause j := literal_mem_iff (i,sign) _
    simp only [he] at hm
    apply rename_executes_to _ memberEmbedding g hm
    · funext k;fin_cases k <;> rfl
    · funext k;fin_cases k <;> rfl
    · intro k hk;fin_cases k <;> first | rfl | exact (hk 0 rfl).elim | exact (hk 1 rfl).elim | exact (hk 2 rfl).elim | exact (hk 3 rfl).elim | exact (hk 4 rfl).elim | exact (hk 5 rfl).elim | exact (hk 6 rfl).elim | exact (hk 7 rfl).elim
  have hc : (clear (1 : Fin 13)).Executes g
      (state [] target [decide ((i,sign)∈F.clause j)] [] [] [] [] [] payload iv jv [] [])
      (state [] [] [decide ((i,sign)∈F.clause j)] [] [] [] [] [] payload iv jv [] []) (target.length+1) := by
    convert clear_executes g (1 : Fin 13)
      (state [] target [decide ((i,sign)∈F.clause j)] [] [] [] [] [] payload iv jv [] []) using 1
    funext k;fin_cases k <;> rfl
  refine ⟨14*i.val+14+((5*payload.length+2)+((5*j.val+2)+(cl+(1+(cm+(target.length+1)+2)+2)+2)+2)+2)+2,
    seq_executes _ _ g hw (seq_executes _ _ g hp (seq_executes _ _ g hi
      (seq_executes _ _ g hlookup (seq_executes _ _ g hpush (seq_executes _ _ g hmem hc))))),?_⟩
  have hlen : (CNF.clauseBits (F.clause j)).length≤payload.length := by
    apply member_length_le
    exact List.mem_map.mpr ⟨F.clause j,List.mem_ofFn.mpr ⟨j,rfl⟩,rfl⟩
  have htarget : target.length=2*i.val+2 := by simp [target,CNF.literalBits]
  change cm≤40*((CNF.clauseBits (F.clause j)).length+target.length+1)^2 at hbm
  change cl≤(j.val+1)*(6*payload.length+14)+1 at hbl
  rw [htarget] at hbm ⊢
  let N := payload.length+i.val+j.val+1
  have hN : 1≤N := by dsimp [N];omega
  have hsize : (CNF.clauseBits (F.clause j)).length+(2*i.val+2)+1≤3*N := by dsimp [N];omega
  have hsq := Nat.pow_le_pow_left hsize 2
  have hj : j.val+1≤N := by dsimp [N];omega
  have hpN : 6*payload.length+14≤14*N := by dsimp [N];omega
  have hprod := Nat.mul_le_mul hj hpN
  change _ ≤ 500*N^2
  have hlin : 16*i.val+5*payload.length+5*j.val+35≤35*N := by dsimp [N];omega
  nlinarith

lemma program_queryFree (sign : Bool) : (program sign).QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ (LiteralWord.program_queryFree sign))
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (rename_queryFree _ _ ClauseLookup.program_queryFree)
          (seq_queryFree _ _ (push_queryFree _ _)
            (seq_queryFree _ _ (rename_queryFree _ _ LiteralMembership.program_queryFree) (clear_queryFree _))))))

end HiddenCircuits.Complexity.CNFCloneEmitter.Incidence
