import HiddenCircuits.DH.Runtime.WordArrayCore

/-! A fixed literal word-array update block. Canonical arrays are consumed and
reconstructed; the unary index and replacement word are preserved. -/
namespace HiddenCircuits.DH.Runtime.WordArray
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

noncomputable def replaceBody : OracleBlock 7 := seq parse (seq (clear 5)
  (seq (clear 7) (seq (copyOn 2 5 6 (by decide) (by decide) (by decide)) emit)))
noncomputable def replaceOne : OracleBlock 7 := branchPop 0 skip replaceBody replaceBody
noncomputable def finish : OracleBlock 7 := seq (reverseOn 0 4 (by decide)) (reverseOn 4 0 (by decide))
noncomputable def replaceFinish : OracleBlock 7 := seq replaceOne finish

/-- No parameter of this finite program depends on the array, index, or word. -/
noncomputable def update : OracleBlock 7 := seq (copyOn 1 3 6 (by decide) (by decide) (by decide))
  (seq skipLoop replaceFinish)

lemma replaceBody_executes (g : BitString → ℕ) (index value acc old rest : BitString) :
    replaceBody.Executes g (state (pairBits old rest) index value [] acc [] [] [])
      (state rest index value [] ((wordChunk value).reverse++acc) [] [] [])
      (6*old.length+11*value.length+23) := by
  have h1 : (clear (5 : Fin 8)).Executes g (state rest index value [] acc old [] [true])
      (state rest index value [] acc [] [] [true]) (old.length+1) := by
    convert clear_executes g (5 : Fin 8) (state rest index value [] acc old [] [true]) using 1
    funext i;fin_cases i <;> simp [state]
  have h2 : (clear (7 : Fin 8)).Executes g (state rest index value [] acc [] [] [true])
      (state rest index value [] acc [] [] []) 2 := by
    convert clear_executes g (7 : Fin 8) (state rest index value [] acc [] [] [true]) using 1
    funext i;fin_cases i <;> simp [state]
  have h3 : (copyOn (2 : Fin 8) 5 6 (by decide) (by decide) (by decide)).Executes g
      (state rest index value [] acc [] [] []) (state rest index value [] acc value [] [])
      (5*value.length+2) := by
    convert copyOn_executes g (2 : Fin 8) 5 6 (by decide) (by decide) (by decide)
      (state rest index value [] acc [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  convert seq_executes _ _ g (parse_executes g index value [] acc old rest)
    (seq_executes _ _ g h1 (seq_executes _ _ g h2
      (seq_executes _ _ g h3 (emit_executes g rest index value [] acc value)))) using 1 <;> omega

lemma replaceOne_cons (g : BitString → ℕ) (index value acc w : BitString) (ws : List BitString) :
    replaceOne.Executes g (state (encodeBitList (w::ws)) index value [] acc [] [] [])
      (state (encodeBitList ws) index value [] ((wordChunk value).reverse++acc) [] [] [])
      (6*w.length+11*value.length+25) := by
  convert branchPop_true 0 skip replaceBody replaceBody g rfl
    (s:=state (encodeBitList (w::ws)) index value [] acc [] [] [])
    (by rw [encodeBitList,pop_data];exact replaceBody_executes g index value acc w (encodeBitList ws)) using 1 <;> omega

lemma replaceOne_nil (g : BitString → ℕ) (index value acc : BitString) :
    replaceOne.Executes g (state [] index value [] acc [] [] [])
      (state [] index value [] acc [] [] []) 3 :=
  branchPop_empty 0 skip replaceBody replaceBody g rfl
    (by simpa using skip_executes g (state [] index value [] acc [] [] []))

lemma finish_executes (g : BitString → ℕ) (rest index value acc : BitString) :
    finish.Executes g (state rest index value [] acc [] [] [])
      (store (acc.reverse++rest) index value) (4*rest.length+2*acc.length+4) := by
  have h1 : (reverseOn (0 : Fin 8) 4 (by decide)).Executes g
      (state rest index value [] acc [] [] []) (state [] index value [] (rest.reverse++acc) [] [] [])
      (2*rest.length+1) := by
    convert reverseOn_executes g (0 : Fin 8) 4 (by decide) (state rest index value [] acc [] [] []) using 1
    funext i;fin_cases i <;> simp [state]
  have h2 : (reverseOn (4 : Fin 8) 0 (by decide)).Executes g
      (state [] index value [] (rest.reverse++acc) [] [] [])
      (store (acc.reverse++rest) index value) (2*(rest.length+acc.length)+1) := by
    convert reverseOn_executes g (4 : Fin 8) 0 (by decide)
      (state [] index value [] (rest.reverse++acc) [] [] []) using 1
    · funext i;fin_cases i <;> simp [state,store,List.reverse_append]
    · simp [state]
  convert seq_executes _ _ g h1 h2 using 1 <;> omega

lemma replaceFinish_executes (g : BitString → ℕ) (index value acc : BitString) (ws : List BitString) :
    ∃t, replaceFinish.Executes g (state (encodeBitList ws) index value [] acc [] [] [])
      (store (acc.reverse++encodeBitList (ws.set 0 value)) index value) t ∧
      t≤6*(encodeBitList ws).length+15*value.length+2*acc.length+35 := by
  cases ws with
  | nil =>
    have h := seq_executes _ _ g (replaceOne_nil g index value acc) (finish_executes g [] index value acc)
    refine ⟨_,by simpa [encodeBitList] using h,?_⟩
    simp [encodeBitList];omega
  | cons w ws =>
    have h := seq_executes _ _ g (replaceOne_cons g index value acc w ws)
      (finish_executes g (encodeBitList ws) index value ((wordChunk value).reverse++acc))
    refine ⟨6*w.length+11*value.length+25+(4*(encodeBitList ws).length+2*((wordChunk value).reverse++acc).length+4)+2,?_,?_⟩
    · simpa [encodeBitList_eq_chunks,List.reverse_append,List.append_assoc] using h
    · simp only [List.length_append,List.length_reverse,wordChunk,List.length_cons,pairBits_length,List.length_nil]
      simp only [encodeBitList,List.length_cons,pairBits_length]
      omega

lemma take_set_drop (ws : List BitString) (j : ℕ) (value : BitString) :
    ws.take j ++ (ws.drop j).set 0 value=ws.set j value := by
  induction j generalizing ws with
  | zero => simp
  | succ j ih =>
    cases ws with
    | nil => simp
    | cons w ws => simpa using congrArg (List.cons w) (ih ws)

lemma encode_take_length (ws : List BitString) (j : ℕ) :
    (encodeBitList (ws.take j)).length≤(encodeBitList ws).length := by
  have he : encodeBitList (ws.take j) ++ encodeBitList (ws.drop j)=encodeBitList ws := by
    rw [←encodeBitList_append,List.take_append_drop]
  have hl := congrArg List.length he
  rw [List.length_append] at hl
  omega

def updateBound (encodedLength indexLength wordLength : ℕ) : ℕ :=
  indexLength*(11*encodedLength+20)+8*encodedLength+5*indexLength+15*wordLength+42

/-- Exact operational random update, including unchanged out-of-range arrays,
with all work physically cleared and both read-only inputs preserved. -/
theorem update_executes (g : BitString → ℕ) (ws : List BitString) (j : ℕ) (value : BitString) :
    ∃t, update.Executes g (store (encodeBitList ws) (List.replicate j true) value)
      (store (encodeBitList (ws.set j value)) (List.replicate j true) value) t ∧
      t≤updateBound (encodeBitList ws).length j value.length := by
  have hc : (copyOn (1 : Fin 8) 3 6 (by decide) (by decide) (by decide)).Executes g
      (store (encodeBitList ws) (List.replicate j true) value)
      (state (encodeBitList ws) (List.replicate j true) value (List.replicate j true) [] [] [] []) (5*j+2) := by
    convert copyOn_executes g (1 : Fin 8) 3 6 (by decide) (by decide) (by decide)
      (store (encodeBitList ws) (List.replicate j true) value) rfl using 1
    · funext i;fin_cases i <;> simp [state,store]
    · simp [state,store]
  obtain ⟨a,ha,hab⟩ := skipLoop_execution g (List.replicate j true) value [] ws j
  simp only [List.append_nil] at ha
  obtain ⟨b,hb,hbb⟩ := replaceFinish_executes g (List.replicate j true) value
    (encodeBitList (ws.take j)).reverse (ws.drop j)
  have h := seq_executes _ _ g hc (seq_executes _ _ g (whilePop_executes _ _ _ g ha) hb)
  refine ⟨5*j+2+(a+b+2)+2,?_,?_⟩
  · simpa only [List.reverse_reverse,←encodeBitList_append,take_set_drop] using h
  · have hd := CNFCloneEmitter.ClauseLookup.encode_drop_length ws j
    have ht := encode_take_length ws j
    simp only [List.length_reverse] at hbb
    unfold updateBound
    omega

lemma replaceBody_queryFree : replaceBody.QueryFree := seq_queryFree _ _ parse_queryFree
  (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) emit_queryFree)))
lemma replaceOne_queryFree : replaceOne.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree replaceBody_queryFree replaceBody_queryFree
lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (reverseOn_queryFree _ _ _) (reverseOn_queryFree _ _ _)
lemma replaceFinish_queryFree : replaceFinish.QueryFree := seq_queryFree _ _ replaceOne_queryFree finish_queryFree
lemma update_queryFree : update.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ skipLoop_queryFree replaceFinish_queryFree)


lemma updateBound_polynomial (L j W : ℕ) : updateBound L j W≤100*(L+j+W+1)^2 := by
  unfold updateBound
  nlinarith

theorem update_executes_polynomial (g : BitString → ℕ) (ws : List BitString) (j : ℕ) (value : BitString) :
    ∃t, update.Executes g (store (encodeBitList ws) (List.replicate j true) value)
      (store (encodeBitList (ws.set j value)) (List.replicate j true) value) t ∧
      t≤100*((encodeBitList ws).length+j+value.length+1)^2 := by
  obtain ⟨t,ht,hb⟩ := update_executes g ws j value
  exact ⟨t,ht,hb.trans (updateBound_polynomial _ _ _)⟩

theorem update_out_of_range (g : BitString → ℕ) (ws : List BitString) (j : ℕ) (value : BitString)
    (hj : ws.length≤j) :
    ∃t, update.Executes g (store (encodeBitList ws) (List.replicate j true) value)
      (store (encodeBitList ws) (List.replicate j true) value) t ∧
      t≤updateBound (encodeBitList ws).length j value.length := by
  simpa only [List.set_eq_of_length_le hj] using update_executes g ws j value

noncomputable def updateOn {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename update φ

/-- Framed update writes only the selected array port; all unselected ambient
stacks and both public input ports are exactly preserved. -/
theorem updateOn_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (ws : List BitString) (j : ℕ) (value : BitString)
    (hs : s∘φ=store (encodeBitList ws) (List.replicate j true) value) :
    ∃t, (updateOn φ).Executes g s (Function.update s (φ 0) (encodeBitList (ws.set j value))) t ∧
      t≤updateBound (encodeBitList ws).length j value.length := by
  obtain ⟨t,ht,hb⟩ := update_executes g ws j value
  refine ⟨t,?_,hb⟩
  apply rename_executes_to update φ g ht hs
  · have he : (Function.update s (φ 0) (encodeBitList (ws.set j value)))∘φ =
        Function.update (s∘φ) 0 (encodeBitList (ws.set j value)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 0).symm _ _

lemma updateOn_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (updateOn φ).QueryFree :=
  rename_queryFree _ _ update_queryFree

/-- Read-only access reuses the independently verified canonical list lookup. -/
def readEmbedding : Fin 7 ↪ Fin 8 := ⟨Fin.castSucc,Fin.castSucc_injective 7⟩
noncomputable def read : OracleBlock 7 := rename GraphReduction.Runtime.listLookup readEmbedding

lemma read_executes (g : BitString → ℕ) (ws : List BitString) (j : ℕ) :
    ∃t, read.Executes g (store (encodeBitList ws) (List.replicate j true) [])
      (store (encodeBitList ws) (List.replicate j true) (ws[j]?.getD [])) t ∧
      t≤GraphReduction.Runtime.lookupBound (encodeBitList ws).length j := by
  obtain ⟨t,ht,hb⟩ := GraphReduction.Runtime.listLookup_executes g ws j
  refine ⟨t,?_,hb⟩
  apply rename_executes_to GraphReduction.Runtime.listLookup readEmbedding g ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim

lemma read_queryFree : read.QueryFree := rename_queryFree _ _ GraphReduction.Runtime.listLookup_queryFree

noncomputable def readOn {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : OracleBlock k := rename read φ

theorem readOn_executes {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (ws : List BitString) (j : ℕ)
    (hs : s∘φ=store (encodeBitList ws) (List.replicate j true) []) :
    ∃t, (readOn φ).Executes g s (Function.update s (φ 2) (ws[j]?.getD [])) t ∧
      t≤GraphReduction.Runtime.lookupBound (encodeBitList ws).length j := by
  obtain ⟨t,ht,hb⟩ := read_executes g ws j
  refine ⟨t,?_,hb⟩
  apply rename_executes_to read φ g ht hs
  · have he : (Function.update s (φ 2) (ws[j]?.getD []))∘φ =
        Function.update (s∘φ) 2 (ws[j]?.getD []) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 2).symm _ _

lemma readOn_queryFree {k : ℕ} (φ : Fin 8 ↪ Fin (k+1)) : (readOn φ).QueryFree :=
  rename_queryFree _ _ read_queryFree

end HiddenCircuits.DH.Runtime.WordArray
