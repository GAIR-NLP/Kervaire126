module

import all KIP126.Literature.BocksteinOriginalSuccessor
import all KIP126.Literature.BocksteinSequenceComparison

/-! Successor compatibility of tower spectral sequences from
differential squares on valid pages. -/

namespace KIP126.Literature.BocksteinComparison.Sequence
open KIP126.AdamsSynthetic KIP126.Literature.Paper38OriginalSuccessor
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private def originalToNormalized
    (S : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1)) :
    FromFirstMorphism S (normalizedAdamsSequence S h0 hd) where
  toSSDataMorphism := SSDataMorphism.id S.ssData
  r₀_eq := h0
  diffDeg_eq := funext hd
  comm_d r hr p := by
    rcases S with ⟨⟨r₀, D, δ, d⟩, hdd, hZ, hB⟩
    change r₀ = 2 at h0
    subst r₀
    have hδ : δ = fun r => (r,r-1) := funext hd
    subst δ
    change 2 ≤ r at hr
    simp only [SSDataMorphism.pageMapAt, SSDataMorphism.pageMap_id,
      normalizedAdamsSequence, if_pos hr, normalizedDifferential,
      eqToHom_refl, Category.id_comp, Category.comp_id]

private def normalizedToOriginal
    (S : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1)) :
    FromFirstMorphism (normalizedAdamsSequence S h0 hd) S where
  toSSDataMorphism := SSDataMorphism.id S.ssData
  r₀_eq := h0.symm
  diffDeg_eq := (funext hd).symm
  comm_d r hr p := by
    rcases S with ⟨⟨r₀, D, δ, d⟩, hdd, hZ, hB⟩
    change r₀ = 2 at h0
    subst r₀
    have hδ : δ = fun r => (r,r-1) := funext hd
    subst δ
    change 2 ≤ r at hr
    simp only [SSDataMorphism.pageMapAt, SSDataMorphism.pageMap_id,
      normalizedAdamsSequence, if_pos hr, normalizedDifferential,
      eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem normalizedToOriginal_pageMap
    (S : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1)) (r : ℤ) (p : ℤ × ℤ) :
    (normalizedToOriginal S h0 hd).pageMap r p =
      eqToHom (by change (S.ssData p).page ↑(r-2).toNat = (S.ssData p).page ↑(r-S.r₀).toNat
                  rw [h0]) := by
  unfold FromFirstMorphism.pageMap SSDataMorphism.pageMapAt
  change (SSDataMorphism.id S.ssData).pageMap p _ ≫ _ = _
  rw [SSDataMorphism.pageMap_id, Category.id_comp]

/-- The identity SSData comparison respects the same original canonical successor. -/
private theorem normalizedToOriginal_successor
    (S : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1))
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (pageHomologyIso (normalizedAdamsSequence S h0 hd) r p hr).hom ≫
      centeredHomologyMap (normalizedToOriginal S h0 hd) r p hr =
    eqToHom (by change (S.ssData p).page ↑(r+1-2).toNat =
                    (S.ssData p).page ↑(r+1-S.r₀).toNat
                rw [h0]) ≫
      (pageHomologyIso S r p (by rw [h0]; exact hr)).hom := by
  rw [← normalizedToOriginal_pageMap S h0 hd]
  exact canonicalSuccessor_naturality (normalizedToOriginal S h0 hd) r p hr

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {X Y : C} {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
  (S S' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
  (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1))
  (h0' : S'.r₀ = 2) (hd' : ∀ r, S'.diffDeg r = (r,r-1))
  (P : TowerSequencePresentation unit T S.ssData (normalizedDifferential S h0 hd))
  (Q : TowerSequencePresentation unit U S'.ssData (normalizedDifferential S' h0' hd'))
  (e : X ≅ Y)

/-- The same ambient tower comparison on original records, with valid-page squares. -/
private def presentedOriginalMap : FromFirstMorphism S S' where
  toSSDataMorphism := presentedDataMap P Q e
  r₀_eq := h0.trans h0'.symm
  diffDeg_eq := (funext hd).trans (funext hd').symm
  comm_d r hr p := by
    have h := presentedPageIso_differential P Q e r (by rw [←h0]; exact hr) p
    rcases S with ⟨⟨r₀, D, δ, d⟩, hdd, hZ, hB⟩
    rcases S' with ⟨⟨r₀', D', δ', d'⟩, hdd', hZ', hB'⟩
    change r₀ = 2 at h0
    change r₀' = 2 at h0'
    subst r₀
    subst r₀'
    have hδ : δ = fun r => (r,r-1) := funext hd
    have hδ' : δ' = fun r => (r,r-1) := funext hd'
    subst δ
    subst δ'
    unfold normalizedDifferential at h
    dsimp only [presentedPageIso] at h
    simpa only [SSDataMorphism.pageMapAt, eqToHom_refl,
      Category.id_comp, Category.comp_id] using h

/-- The quotient isomorphism with the specified page-numbering transports. -/
private theorem presentedOriginalMap_pageMap (r : ℤ) (p : ℤ × ℤ) :
    (presentedOriginalMap S S' h0 hd h0' hd' P Q e).pageMap r p =
      eqToHom (by change (S.ssData p).page ↑(r-S.r₀).toNat =
                      (S.ssData p).page ↑(r-2).toNat
                  rw [h0]) ≫
        (presentedPageIso P Q e p ↑(r-2).toNat).hom ≫
      eqToHom (by change (S'.ssData p).page ↑(r-2).toNat =
                      (S'.ssData p).page ↑(r-S'.r₀).toNat
                  rw [h0']) := by
  rcases S with ⟨⟨r₀, D, δ, d⟩, hdd, hZ, hB⟩
  rcases S' with ⟨⟨r₀', D', δ', d'⟩, hdd', hZ', hB'⟩
  change r₀ = 2 at h0
  change r₀' = 2 at h0'
  subst r₀
  subst r₀'
  unfold FromFirstMorphism.pageMap SSDataMorphism.pageMapAt
  simp only [presentedOriginalMap, presentedPageIso,
    eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem presentedOriginalMap_pageMap_isIso (r : ℤ) (p : ℤ × ℤ) :
    IsIso ((presentedOriginalMap S S' h0 hd h0' hd' P Q e).pageMap r p) := by
  unfold FromFirstMorphism.pageMap SSDataMorphism.pageMapAt
  change IsIso ((presentedPageIso P Q e p ↑(r-S.r₀).toNat).hom ≫ _)
  infer_instance

/-- The original centered complexes are isomorphic on every valid page. -/
private def presentedOriginalComplexIso (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    S.pageShortComplex r (p-S.diffDeg r) ≅ S'.pageShortComplex r (p-S'.diffDeg r) := by
  let f := presentedOriginalMap S S' h0 hd h0' hd' P Q e
  let g := centeredComplexMap f r p (by rw [h0]; exact hr)
  haveI (q : ℤ × ℤ) : IsIso (f.pageMap r q) :=
    presentedOriginalMap_pageMap_isIso S S' h0 hd h0' hd' P Q e r q
  haveI : IsIso g.τ₁ := by change IsIso (f.pageMap r _ ≫ eqToHom _); infer_instance
  haveI : IsIso g.τ₂ := by change IsIso (f.pageMap r _ ≫ eqToHom _); infer_instance
  haveI : IsIso g.τ₃ := by change IsIso (f.pageMap r _ ≫ eqToHom _); infer_instance
  letI : IsIso g := ShortComplex.isIso_of_isIso g
  exact asIso g

private def presentedOriginalHomologyIso (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (S.pageShortComplex r (p-S.diffDeg r)).homology ≅
      (S'.pageShortComplex r (p-S'.diffDeg r)).homology :=
  ShortComplex.homologyMapIso
    (presentedOriginalComplexIso S S' h0 hd h0' hd' P Q e r hr p)

/-- The original records' canonical successor square, with the actual tower
quotient maps and their induced homology isomorphism. -/
private theorem presentedOriginalCanonicalSuccessor_comm
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (pageHomologyIso S r p (by rw [h0]; exact hr)).hom ≫
      (presentedOriginalHomologyIso S S' h0 hd h0' hd' P Q e r hr p).hom =
    (presentedOriginalMap S S' h0 hd h0' hd' P Q e).pageMap (r+1) p ≫
      (pageHomologyIso S' r p (by rw [h0']; exact hr)).hom := by
  exact canonicalSuccessor_naturality
    (presentedOriginalMap S S' h0 hd h0' hd' P Q e) r p (by rw [h0]; exact hr)

end
end KIP126.Literature.BocksteinComparison.Sequence
