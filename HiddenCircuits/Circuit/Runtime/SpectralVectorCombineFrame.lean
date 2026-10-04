import HiddenCircuits.Circuit.Runtime.SpectralVectorCombine

/-! Ordinary equal-length vector and arbitrary caller-frame interfaces. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralVectorCombine
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic

theorem program_zip_executes (g : BitString → ℕ) (scale : ℤ) (xs ys : List ℤ) (hlen : xs.length=ys.length) :
    ∃ t, program.Executes g (inputStore (signedBits scale) (encodeBitList (xs.map signedBits)) (encodeBitList (ys.map signedBits)))
      (Function.update (fun _ : Fin 21 => ([]:BitString)) 0
        (encodeBitList ((List.zipWith (fun x y => y+scale*x) xs ys).map signedBits))) t ∧
      t≤time.eval ((signedBits scale).length+(encodeBitList (xs.map signedBits)).length+(encodeBitList (ys.map signedBits)).length) := by
  have hx : (xs.zip ys).map (fun p => signedBits p.1)=xs.map signedBits := by
    change (xs.zip ys).map (signedBits ∘ Prod.fst)=xs.map signedBits
    rw [←List.map_map,List.map_fst_zip hlen.le]
  have hy : (xs.zip ys).map (fun p => signedBits p.2)=ys.map signedBits := by
    change (xs.zip ys).map (signedBits ∘ Prod.snd)=ys.map signedBits
    rw [←List.map_map,List.map_snd_zip hlen.ge]
  have ho : output scale (xs.zip ys)=List.zipWith (fun x y => y+scale*x) xs ys := by
    change (xs.zip ys).map (fun p : ℤ×ℤ => p.2+scale*p.1)=_
    exact List.map_uncurry_zip_eq_zipWith (f:=fun x y : ℤ => y+scale*x) (l:=xs) (l':=ys)
  simpa only [inputLength,hx,hy,ho] using program_executes g scale (xs.zip ys)

noncomputable def programOn {k : ℕ} (φ : Fin 21 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 21 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (scale : ℤ) (xs ys : List ℤ) (hlen : xs.length=ys.length)
    (hs : s∘φ=inputStore (signedBits scale) (encodeBitList (xs.map signedBits)) (encodeBitList (ys.map signedBits))) :
    ∃ t, (programOn φ).Executes g s
      (Function.update (Function.update (Function.update s (φ 0)
        (encodeBitList ((List.zipWith (fun x y => y+scale*x) xs ys).map signedBits))) (φ 1) []) (φ 2) []) t ∧
      t≤time.eval ((signedBits scale).length+(encodeBitList (xs.map signedBits)).length+(encodeBitList (ys.map signedBits)).length) := by
  obtain ⟨t,ht,hb⟩ := program_zip_executes g scale xs ys hlen
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update (Function.update (Function.update s (φ 0)
        (encodeBitList ((List.zipWith (fun x y => y+scale*x) xs ys).map signedBits))) (φ 1) []) (φ 2) [])∘φ=
        Function.update (Function.update (Function.update (s∘φ) 0
          (encodeBitList ((List.zipWith (fun x y => y+scale*x) xs ys).map signedBits))) 1 []) 2 [] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj;rw [Function.update_of_ne (hj 2).symm,Function.update_of_ne (hj 1).symm,Function.update_of_ne (hj 0).symm]

theorem programOn_queryFree {k : ℕ} (φ : Fin 21 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralVectorCombine
