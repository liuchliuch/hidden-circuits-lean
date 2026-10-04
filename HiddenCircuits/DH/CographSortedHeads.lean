import HiddenCircuits.DH.HeadProfileKeys
import HiddenCircuits.DH.CographFamilySpec

/-! Executable sparse head classification, exact global cardinal keys, and stable
sorting, bundled into one ordinary-row preprocessing stage. -/
namespace HiddenCircuits.DH.CographSortedHeads
open SimpleGraph LexBFSModel SliceHeads LinearBuckets
variable {n : ℕ}

def run (rows : Vector (List (Fin n)) n) (normal : Bool) (events : List (Event (Fin n))) : Children n :=
  let es := NonpreferredHeads.classified rows normal events
  let keys := HeadProfileCounts.profileKeys rows es.1 normal
  let out := SortProfileHeads.run keys.keys es.1
  ⟨out.rows,es.2+keys.accesses+out.accesses⟩

lemma classified_heads_nodup (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (s : Bool) (events : List (Event (Fin n))) (hn : (events.map Event.vertex).Nodup) :
    ((NonpreferredHeads.classified rows s events).1.map Prod.snd).Nodup := by
  rw [NonpreferredHeads.classified_values G rows hr]
  exact hn.sublist ((List.filter_sublist.map Prod.snd).trans (parentEntries_build_child_sublist events))

lemma row_perm (rows : Vector (List (Fin n)) n) (s : Bool)
    (events : List (Event (Fin n))) (r : Fin n) :
    ((run rows s events).rows[r.val]).Perm ((NonpreferredHeads.construct rows s events).rows[r.val]) := by
  have h := SortProfileHeads.run_row_perm
    (HeadProfileCounts.profileKeys rows (NonpreferredHeads.classified rows s events).1 s).keys
    (NonpreferredHeads.classified rows s events).1 r
  rw [←NonpreferredHeads.group_get,NonpreferredHeads.classified_group] at h
  exact h

lemma mem_iff (rows : Vector (List (Fin n)) n) (s : Bool)
    (events : List (Event (Fin n))) (r x : Fin n) :
    x∈(run rows s events).rows[r.val] ↔ (r,x)∈(NonpreferredHeads.classified rows s events).1 := by
  have h := SortProfileHeads.run_row_perm
    (HeadProfileCounts.profileKeys rows (NonpreferredHeads.classified rows s events).1 s).keys
    (NonpreferredHeads.classified rows s events).1 r
  change x∈(SortProfileHeads.run
    (HeadProfileCounts.profileKeys rows (NonpreferredHeads.classified rows s events).1 s).keys
    (NonpreferredHeads.classified rows s events).1).rows[r.val] ↔ _
  rw [h.mem_iff]
  constructor
  · intro hm
    obtain ⟨⟨a,b⟩,hp,hb⟩ := List.mem_map.mp hm
    have ha : a=r := by simpa using (List.mem_filter.mp hp).2
    subst a; dsimp only at hb; subst b
    exact (List.mem_filter.mp hp).1
  · intro hm; exact List.mem_map.mpr ⟨(r,x),List.mem_filter.mpr ⟨hm,by simp⟩,rfl⟩

lemma normal_card_order (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hrows : ∀v:Fin n, (rows[v.val]).Nodup) (events : List (Event (Fin n)))
    (hn : (events.map Event.vertex).Nodup) (r : Fin n) :
    ((run rows true events).rows[r.val]).Pairwise
      (fun x y => (pivotProfile G r y).ncard≤(pivotProfile G r x).ncard) := by
  let es := (NonpreferredHeads.classified rows true events).1
  let keys := (HeadProfileCounts.profileKeys rows es true).keys
  have he := classified_heads_nodup G rows hr true events hn
  have hsort := SortProfileHeads.run_row_descending keys es r
  apply hsort.imp_of_mem
  intro x y hx hy hxy
  have hxE := (mem_iff rows true events r x).mp hx
  have hyE := (mem_iff rows true events r y).mp hy
  have hkx := HeadProfileCounts.profileKeys_normal_get G rows hr hrows es he r x hxE
  have hky := HeadProfileCounts.profileKeys_normal_get G rows hr hrows es he r y hyE
  have hnum : (keys[y.val]).val≤(keys[x.val]).val := hxy
  change (keys[x.val]).val=_ at hkx
  change (keys[y.val]).val=_ at hky
  rwa [hkx,hky] at hnum

lemma complement_card_order (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hrows : ∀v:Fin n, (rows[v.val]).Nodup) (events : List (Event (Fin n)))
    (hn : (events.map Event.vertex).Nodup) (r : Fin n) :
    ((run rows false events).rows[r.val]).Pairwise
      (fun x y => (pivotProfile Gᶜ r y).ncard≤(pivotProfile Gᶜ r x).ncard) := by
  let es := (NonpreferredHeads.classified rows false events).1
  let keys := (HeadProfileCounts.profileKeys rows es false).keys
  have he := classified_heads_nodup G rows hr false events hn
  have hadj (x : Fin n) (hx : (r,x)∈es) : G.Adj r x := by
    have hv := NonpreferredHeads.classified_values G rows hr false events
    change (r,x)∈(NonpreferredHeads.classified rows false events).1 at hx
    rw [hv] at hx
    simpa using (List.mem_filter.mp hx).2
  have hsort := SortProfileHeads.run_row_descending keys es r
  apply hsort.imp_of_mem
  intro x y hx hy hxy
  have hxE := (mem_iff rows false events r x).mp hx
  have hyE := (mem_iff rows false events r y).mp hy
  have hkx := HeadProfileCounts.profileKeys_complement_get G rows hr hrows es he r x hxE (hadj x hxE)
  have hky := HeadProfileCounts.profileKeys_complement_get G rows hr hrows es he r y hyE (hadj y hyE)
  have hnum : (keys[y.val]).val≤(keys[x.val]).val := hxy
  change (keys[x.val]).val=_ at hkx
  change (keys[y.val]).val=_ at hky
  rwa [hkx,hky] at hnum

lemma accesses (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (s : Bool) (events : List (Event (Fin n))) (hn : (events.map Event.vertex).Nodup) :
    (run rows s events).accesses≤36*(∑i:Fin n,rows[i.val].length)+51*events.length+28*n+4 := by
  have he := NonpreferredHeads.classified_accesses rows s events
  have hlen := NonpreferredHeads.classified_length rows s events
  have hnE := classified_heads_nodup G rows hr s events hn
  have hk := HeadProfileCounts.profileKeys_accesses rows (NonpreferredHeads.classified rows s events).1 hnE s
  have hs := SortProfileHeads.run_accesses
    (HeadProfileCounts.profileKeys rows (NonpreferredHeads.classified rows s events).1 s).keys
    (NonpreferredHeads.classified rows s events).1
  simp only [run]
  omega

end HiddenCircuits.DH.CographSortedHeads
