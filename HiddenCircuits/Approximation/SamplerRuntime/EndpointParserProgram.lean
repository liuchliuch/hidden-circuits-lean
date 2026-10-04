import HiddenCircuits.Approximation.SamplerRuntime.EndpointParserFront

/-! Total36-stack endpoint parser, including canonical syntax and all monotonicity
checks. The validity flag agrees with the literal decoder on every binary string. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
open Complexity OracleBlock GraphReduction MonotoneEndpointEncoding
set_option maxHeartbeats 900000

def lowCopied (xs : BitString) : Store 35 := Function.update (prepared xs) 17 (second xs).left
def seeded (xs : BitString) : Store 35 := Function.update (lowCopied xs) 18 (third xs).left
def output (xs : BitString) : Store 35 := fun i =>
  if i.val=0 then xs else if i.val=1 then (first xs).left else if i.val=2 then (second xs).left
  else if i.val=3 then (third xs).left else if i.val=4 then [valid xs] else []
def scanMap : Fin 24 ↪ Fin 36 where
  toFun i := if i.val=0 then 1 else if i.val=1 then 15 else if i.val=2 then 16
    else if i.val=3 then 17 else if i.val=4 then 18 else if i.val=5 then 14
    else if i.val=6 then 4 else if i.val=7 then 19 else if i.val=8 then 20
    else if i.val=9 then 21 else if i.val=10 then 22 else if i.val=11 then 12
    else ⟨i.val+11,by omega⟩
  inj' := by decide +kernel
noncomputable def seed : OracleBlock 35 := seq (copyOn 2 17 8 (by decide) (by decide) (by decide))
  (copyOn 3 18 8 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 35 := seq front (seq seed (rename Scan.program scanMap))

lemma seed_executes (g : BitString → ℕ) (xs : BitString) :
    seed.Executes g (prepared xs) (seeded xs) (5*(second xs).left.length+5*(third xs).left.length+6) := by
  have hl : (copyOn (2:Fin 36) 17 8 (by decide) (by decide) (by decide)).Executes g
      (prepared xs) (lowCopied xs) (5*(second xs).left.length+2) := by
    simpa [prepared,lowCopied] using copyOn_executes g (2:Fin 36) 17 8 (by decide) (by decide) (by decide) (prepared xs) rfl
  have hh : (copyOn (3:Fin 36) 18 8 (by decide) (by decide) (by decide)).Executes g
      (lowCopied xs) (seeded xs) (5*(third xs).left.length+2) := by
    simpa [prepared,lowCopied,seeded] using copyOn_executes g (3:Fin 36) 18 8 (by decide) (by decide) (by decide) (lowCopied xs) rfl
  convert seq_executes _ _ g hl hh using 1 <;> omega

lemma fields_lengths (xs : BitString) : (first xs).left.length≤xs.length ∧
    (second xs).left.length≤xs.length ∧ (third xs).left.length≤xs.length := by
  have h1 := head_lengths xs
  have h2 := head_lengths (first xs).right
  have h3 := head_lengths (second xs).right
  change (first xs).left.length≤xs.length ∧ (first xs).right.length≤xs.length at h1
  change (second xs).left.length≤(first xs).right.length ∧ (second xs).right.length≤(first xs).right.length at h2
  change (third xs).left.length≤(second xs).right.length ∧ (third xs).right.length≤(second xs).right.length at h3
  exact ⟨h1.1,h2.1.trans h1.2,h3.1.trans (h2.2.trans h1.2)⟩
lemma initial_bounded (xs : BitString) : Scan.Bounded xs.length (initial xs) :=
  ⟨(fields_lengths xs).1,by simp [initial],by simp [initial],(fields_lengths xs).2.1,(fields_lengths xs).2.2⟩

lemma scan_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,(rename Scan.program scanMap).Executes g (seeded xs) (output xs) c ∧
      c≤xs.length*(2000*(xs.length+1)+2)+10*xs.length+103 := by
  obtain ⟨c,hc,hb⟩ := Scan.program_executes g (initial xs) (List.replicate (first xs).left.length true) xs.length (initial_bounded xs)
  simp only [List.length_replicate] at hc hb
  refine ⟨c,?_,hb.trans (by gcongr;exact (fields_lengths xs).1)⟩
  apply rename_executes_to Scan.program scanMap g (outerS:=seeded xs) (outerT:=output xs) hc
  · clear hc hb;funext i;fin_cases i <;> rfl
  · clear hc hb;funext i;fin_cases i <;> rfl
  · clear hc hb;intro i hi
    fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 3 rfl) |
      exact False.elim (hi 4 rfl) | exact False.elim (hi 5 rfl) | exact False.elim (hi 6 rfl) | exact False.elim (hi 11 rfl)

noncomputable def time : Polynomial ℕ := 100000*(Polynomial.X+1)^2

theorem program_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,program.Executes g (input xs) (output xs) c ∧ c≤time.eval xs.length := by
  obtain ⟨a,ha,hab⟩ := front_executes g xs
  obtain ⟨b,hb,hbb⟩ := scan_executes g xs
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g (seed_executes g xs) hb),?_⟩
  have hs := fields_lengths xs
  simp only [time,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith [hs.2.1,hs.2.2]
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ front_queryFree
  (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
    (rename_queryFree _ _ Scan.program_queryFree))

theorem output_flag (xs : BitString) : output xs 4=[(decode xs).isSome] := by simp [output,valid_eq_decode]
theorem output_fields {xs : BitString} {E : Input} (h : decode xs=some E) :
    output xs 1=List.replicate E.1 true ∧ output xs 2=encodeBitList (rows E.2.lo) ∧
      output xs 3=encodeBitList (rows E.2.hi) := by
  simpa only [output,ite_false,ite_true] using fields_of_decode h
lemma output_clean (xs : BitString) (i : Fin 36) (h : 5 ≤ i.val) : output xs i=[] := by
  simp [output,show i.val≠0 by omega,show i.val≠1 by omega,show i.val≠2 by omega,show i.val≠3 by omega,show i.val≠4 by omega]
end HiddenCircuits.Approximation.SamplerRuntime.EndpointParser
