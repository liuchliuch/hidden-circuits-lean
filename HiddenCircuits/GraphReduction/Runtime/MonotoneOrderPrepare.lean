import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderState

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneOrderRuntime
open Complexity OracleBlock
set_option maxHeartbeats 900000

noncomputable def xLayer (lower : Bool) : OracleBlock 56 := MonotoneLayer.on xLayerEmbedding lower
lemma xLayer_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(xLayer lower).Executes g (state lower c x y 0) (state lower c x y 1) t ∧ t≤5*x.layer+27 := by
  obtain ⟨t,hc,hb⟩:=MonotoneLayer.on_executes xLayerEmbedding g lower x.side x.probe x.layer (state lower c x y 0) (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,hb⟩
  convert hc using 1
  funext j;fin_cases j <;> rfl

noncomputable def yLayer (lower : Bool) : OracleBlock 56 := MonotoneLayer.on yLayerEmbedding lower
lemma yLayer_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(yLayer lower).Executes g (state lower c x y 1) (state lower c x y 2) t ∧ t≤5*y.layer+27 := by
  obtain ⟨t,hc,hb⟩:=MonotoneLayer.on_executes yLayerEmbedding g lower y.side y.probe y.layer (state lower c x y 1) (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,hb⟩
  convert hc using 1
  funext j;fin_cases j <;> rfl

noncomputable def layerLT (lower : Bool) : OracleBlock 56 := readOnlyLTOn layerLTEmbedding
lemma layerLT_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(layerLT lower).Executes g (state lower c x y 2) (state lower c x y 3) t ∧ t≤6*(layerValue lower x)+14*(layerValue lower y)+15 := by
  obtain ⟨t,hc,hb⟩:=readOnlyLTOn_executes layerLTEmbedding g (state lower c x y 2) (layerValue lower x) (layerValue lower y) (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,hb⟩
  convert hc using 1
  funext j;fin_cases j <;> rfl

noncomputable def layerEQ (lower : Bool) : OracleBlock 56 := GraphVerifier.Runtime.readLengthOn layerEQEmbedding
lemma layerEQ_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(layerEQ lower).Executes g (state lower c x y 3) (state lower c x y 4) t ∧ t≤13*(layerValue lower x+layerValue lower y)+23 := by
  obtain ⟨t,hc,hb⟩:=GraphVerifier.Runtime.readLengthOn_executes layerEQEmbedding g (state lower c x y 3) (List.replicate (layerValue lower x) true) (List.replicate (layerValue lower y) true) (by funext j;fin_cases j <;> rfl)
  simp only [List.length_replicate] at hc hb
  refine ⟨t,?_,hb⟩
  convert hc using 1
  funext j;fin_cases j <;> rfl

noncomputable def trackLT (lower : Bool) : OracleBlock 56 := readOnlyLTOn trackLTEmbedding
lemma trackLT_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(trackLT lower).Executes g (state lower c x y 4) (state lower c x y 5) t ∧ t≤6*x.track+14*y.track+15 := by
  obtain ⟨t,hc,hb⟩:=readOnlyLTOn_executes trackLTEmbedding g (state lower c x y 4) x.track y.track (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,hb⟩
  convert hc using 1
  funext j;fin_cases j <;> rfl

noncomputable def trackGT (lower : Bool) : OracleBlock 56 := readOnlyLTOn trackGTEmbedding
lemma trackGT_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(trackGT lower).Executes g (state lower c x y 5) (state lower c x y 6) t ∧ t≤6*y.track+14*x.track+15 := by
  obtain ⟨t,hc,hb⟩:=readOnlyLTOn_executes trackGTEmbedding g (state lower c x y 5) y.track x.track (by funext j;fin_cases j <;> rfl)
  refine ⟨t,?_,hb⟩
  convert hc using 1
  funext j;fin_cases j <;> rfl

noncomputable def prepare (lower : Bool) : OracleBlock 56 := seq (xLayer lower) (seq (yLayer lower)
  (seq (layerLT lower) (seq (layerEQ lower) (seq (trackLT lower) (trackGT lower)))))

theorem prepare_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    ∃t,(prepare lower).Executes g (state lower c x y 0) (state lower c x y 6) t ∧ t≤100*dirSize x y+330 := by
  obtain ⟨a,ha,hab⟩:=xLayer_executes g lower c x y
  obtain ⟨b,hb,hbb⟩:=yLayer_executes g lower c x y
  obtain ⟨d,hd,hdb⟩:=layerLT_executes g lower c x y
  obtain ⟨e,he,heb⟩:=layerEQ_executes g lower c x y
  obtain ⟨f,hf,hfb⟩:=trackLT_executes g lower c x y
  obtain ⟨h,hh,hhb⟩:=trackGT_executes g lower c x y
  refine ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hd (seq_executes _ _ g he (seq_executes _ _ g hf hh)))),?_⟩
  have hx:=layerValue_le lower x
  have hy:=layerValue_le lower y
  have hc:x.layer+y.layer+x.track+y.track≤dirSize x y:=by simp [dirSize,encodeVertex_length];omega
  omega

lemma prepare_queryFree (lower : Bool) : (prepare lower).QueryFree := seq_queryFree _ _ (MonotoneLayer.on_queryFree _ _)
  (seq_queryFree _ _ (MonotoneLayer.on_queryFree _ _) (seq_queryFree _ _ (readOnlyLTOn_queryFree _)
    (seq_queryFree _ _ (GraphVerifier.Runtime.readLengthOn_queryFree _) (seq_queryFree _ _ (readOnlyLTOn_queryFree _) (readOnlyLTOn_queryFree _)))))
end HiddenCircuits.GraphReduction.Runtime.MonotoneOrderRuntime
