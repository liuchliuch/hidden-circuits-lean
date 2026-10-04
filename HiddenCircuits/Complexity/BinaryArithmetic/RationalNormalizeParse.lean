import HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalizeZero
import HiddenCircuits.Complexity.BinaryArithmetic.SignedNormalize
import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary
import HiddenCircuits.Complexity.GraphVerifier.TwoParse

/-! Total byte-level parsing for rational normalization. Invalid pair words map
to zero; empty signed words, redundant magnitude bits, and negative zero are
interpreted by the explicitly total signed decoder and physically normalized. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
open OracleBlock Polynomial GraphVerifier GraphVerifier.Runtime

def rawValue (xs : BitString) : ℚ :=
  match unpairBits xs with
  | none => 0
  | some (u,v) => (SignedNormalize.value u:ℚ)/(SignedNormalize.value v:ℚ)

lemma parse_invalid_right (xs : BitString) (h : (parse xs).ok=false) : (parse xs).right=[] := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    cases b
    · simp [parse] at h
    · cases xs with
      | nil => rfl
      | cons bit bs => exact parse_invalid_right bs h
termination_by xs.length

lemma rawValue_parse (xs : BitString) : rawValue xs=
    (SignedNormalize.value (parse xs).left:ℚ)/(SignedNormalize.value (parse xs).right:ℚ) := by
  rw [rawValue,parse_spec]
  cases ho:(parse xs).ok
  · simp [ho,parse_invalid_right xs ho,SignedNormalize.value]
  · simp [ho]

@[simp] lemma rawValue_pair (u v : ℤ) : rawValue (pairBits (signedBits u) (signedBits v))=(u:ℚ)/(v:ℚ) := by
  simp [rawValue,unpair_pairBits]

def parseMap : Fin 4 ↪ Fin 16 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 9 else if i.val=2 then 1 else 2
  inj' := by decide +kernel

def parsed (xs : BitString) : Store 15 :=
  Function.update (Function.update (regState (parse xs).left [] []) 0 (parse xs).right) 2 [(parse xs).ok]
noncomputable def parseProgram : OracleBlock 15 :=
  seq (unpairOn parseMap) (seq (clear 2) (moveOn 0 10 1 (by decide) (by decide) (by decide)))

lemma parseProgram_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,parseProgram.Executes g (Function.update (fun _=>[]) 0 xs)
      (regState (parse xs).left (parse xs).right []) c ∧ c≤9*xs.length+15 := by
  have hp : (unpairOn parseMap).Executes g (Function.update (fun _=>[]) 0 xs) (parsed xs)
      (parseCost xs+2*(parse xs).left.length+1) := by
    apply unpairOn_executes
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl)
  have hc : (clear (2:Fin 16)).Executes g (parsed xs)
      (Function.update (regState (parse xs).left [] []) 0 (parse xs).right) 2 := by
    convert clear_executes g (2:Fin 16) (parsed xs) using 1
    funext i;fin_cases i <;> rfl
  have hm : (moveOn (0:Fin 16) 10 1 (by decide) (by decide) (by decide)).Executes g
      (Function.update (regState (parse xs).left [] []) 0 (parse xs).right)
      (regState (parse xs).left (parse xs).right []) (6*(parse xs).right.length+5) := by
    convert moveOn_executes g (0:Fin 16) 10 1 (by decide) (by decide) (by decide)
      (Function.update (regState (parse xs).left [] []) 0 (parse xs).right) rfl using 1
    funext i;fin_cases i <;> simp [regState,RegisterMachine.store,regs]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc hm),?_⟩
  have h1:=unpair_cost_bound xs
  have h2:=(parse_lengths xs).2
  omega

def signedMap (port : Fin 16) (h0:port≠0) (h1:port≠1) (h2:port≠2) : Fin 4 ↪ Fin 16 where
  toFun i := if i.val=0 then port else if i.val=1 then 0 else if i.val=2 then 1 else 2
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def signedLeft : OracleBlock 15 := SignedNormalize.on (signedMap 9 (by decide) (by decide) (by decide))
noncomputable def signedRight : OracleBlock 15 := SignedNormalize.on (signedMap 10 (by decide) (by decide) (by decide))
noncomputable def normalizeWords : OracleBlock 15 := seq signedLeft signedRight

lemma normalizeWords_executes (g : BitString → ℕ) (left right : BitString) :
    ∃c,normalizeWords.Executes g (regState left right [])
      (regState (signedBits (SignedNormalize.value left)) (signedBits (SignedNormalize.value right)) []) c ∧
      c≤5*left.length+5*right.length+36 := by
  obtain ⟨cl,hl,hlb⟩:=SignedNormalize.on_executes (signedMap 9 (by decide) (by decide) (by decide)) g
    (regState left right []) left (by funext i;fin_cases i <;> rfl)
  have hle : Function.update (regState left right [])
      ((signedMap 9 (by decide) (by decide) (by decide)) 0) (signedBits (SignedNormalize.value left))=
      regState (signedBits (SignedNormalize.value left)) right [] := by funext i;fin_cases i <;> rfl
  rw [hle] at hl
  obtain ⟨cr,hr,hrb⟩:=SignedNormalize.on_executes (signedMap 10 (by decide) (by decide) (by decide)) g
    (regState (signedBits (SignedNormalize.value left)) right []) right (by funext i;fin_cases i <;> rfl)
  have hre : Function.update (regState (signedBits (SignedNormalize.value left)) right [])
      ((signedMap 10 (by decide) (by decide) (by decide)) 0) (signedBits (SignedNormalize.value right))=
      regState (signedBits (SignedNormalize.value left)) (signedBits (SignedNormalize.value right)) [] := by
    funext i;fin_cases i <;> rfl
  rw [hre] at hr
  exact ⟨_,seq_executes _ _ g hl hr,by omega⟩

noncomputable def rawProgram : OracleBlock 15 := seq parseProgram (seq normalizeWords dispatch)
noncomputable def rawTime : Polynomial ℕ := dispatchTime.comp (2*X+2)+19*X+55

/-- All raw words, including malformed pairs and noncanonical signed magnitudes,
terminate with the canonical natural-answer word of the explicitly total decoder. -/
theorem rawProgram_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,rawProgram.Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits (rawValue xs))) c ∧
      c≤rawTime.eval xs.length := by
  obtain ⟨cp,hp,hpb⟩:=parseProgram_executes g xs
  obtain ⟨cn,hn,hnb⟩:=normalizeWords_executes g (parse xs).left (parse xs).right
  obtain ⟨cd,hd,hdb⟩:=dispatch_executes g (SignedNormalize.value (parse xs).left) (SignedNormalize.value (parse xs).right)
  rw [←rawValue_parse] at hd
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hn hd),?_⟩
  have hlen:=parse_lengths xs
  have hl:=SignedNormalize.signed_length (parse xs).left
  have hr:=SignedNormalize.signed_length (parse xs).right
  have hm:=polynomial_nat_eval_mono dispatchTime
    (show (signedBits (SignedNormalize.value (parse xs).left)).length+
      (signedBits (SignedNormalize.value (parse xs).right)).length≤2*xs.length+2 by omega)
  dsimp only at hm
  simp only [rawTime,eval_add,eval_mul,eval_ofNat,eval_X,eval_comp]
  omega

lemma parseProgram_queryFree : parseProgram.QueryFree := seq_queryFree _ _ (unpairOn_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _))
lemma normalizeWords_queryFree : normalizeWords.QueryFree :=
  seq_queryFree _ _ (SignedNormalize.on_queryFree _) (SignedNormalize.on_queryFree _)
lemma rawProgram_queryFree : rawProgram.QueryFree := seq_queryFree _ _ parseProgram_queryFree
  (seq_queryFree _ _ normalizeWords_queryFree dispatch_queryFree)

/-- The typed serialized-ratio interface has no certificate parameters. -/
theorem pairProgram_executes (g : BitString → ℕ) (u v : ℤ) :
    ∃c,rawProgram.Executes g (Function.update (fun _=>[]) 0 (pairBits (signedBits u) (signedBits v)))
      (Function.update (fun _=>[]) 0 (RationalOracleEncoding.bits ((u:ℚ)/(v:ℚ)))) c ∧
      c≤rawTime.eval (pairBits (signedBits u) (signedBits v)).length := by
  simpa only [rawValue_pair] using rawProgram_executes g (pairBits (signedBits u) (signedBits v))

/-- Explicit framed interface for attaching the normalizer after a circuit. -/
theorem on_executes {k : ℕ} (φ : Fin 16 ↪ Fin (k+1)) (g : BitString → ℕ)
    (s : Store k) (xs : BitString) (hs:s ∘ φ=Function.update (fun _=>[]) 0 xs) :
    ∃c,(rename rawProgram φ).Executes g s
      (Function.update s (φ 0) (RationalOracleEncoding.bits (rawValue xs))) c ∧c≤rawTime.eval xs.length := by
  obtain ⟨c,hc,hcb⟩:=rawProgram_executes g xs
  refine ⟨c,?_,hcb⟩
  apply rename_executes_to _ φ g hc hs
  · funext i
    have hi:=congrFun hs i
    simp only [Function.comp_apply,Function.update_apply,φ.injective.eq_iff]
    change s (φ i)=_ at hi
    by_cases hz:i=0
    · subst i;simp
    · simp [hz] at hi ⊢;exact hi
  · intro i hi;simp [Ne.symm (hi 0)]

end HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
