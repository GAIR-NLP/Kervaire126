module
import all KIP126.Literature.E2Exactness.Ordinary.ActualE2Exactness

@[expose] section
namespace KIP126.Literature.Standard.ActualE2LES
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Core.SpectralSequence
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def pageTwoIso (X : Spectrum) (p : ℤ × ℤ) :
    ((classical.obj X).ssData p).page 0 ≅ (classical.obj X).Page 2 p :=
  eqToIso (by simp only [Page, classical.firstPage, sub_self, Int.toNat_zero, Nat.cast_zero])

private theorem indexed_map_cast {I : Type*} {C : Type*} [Category C]
    (A B : I → C) (f : ∀ i, A i ⟶ B i) {i j : I} (h : i = j) :
    f i ≫ eqToHom (congrArg B h) = eqToHom (congrArg A h) ≫ f j := by
  subst j
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

private theorem pageTwoIso_natural {X Y : Spectrum} (f : X ⟶ Y) (p : ℤ × ℤ) :
    (classical.map f).toSSDataMorphism.pageMap p 0 ≫ (pageTwoIso Y p).hom =
      (pageTwoIso X p).hom ≫ (classical.map f).pageMap 2 p := by
  have h : (0 : WithTop ℕ) = ↑(2 - (classical.obj X).r₀).toNat := by
    rw [classical.firstPage X]
    rfl
  have hn := indexed_map_cast
    (fun i => ((classical.obj X).ssData p).page i)
    (fun i => ((classical.obj Y).ssData p).page i)
    ((classical.map f).toSSDataMorphism.pageMap p) h
  simp only [pageTwoIso, eqToIso.hom, SpectralSequenceMorphism.pageMap,
    SpectralSequenceMorphism.toPreSSMorphism, PreSSMorphism.pageMap, SSDataMorphism.pageMapAt]
  rw [← Category.assoc, ← hn, Category.assoc, eqToHom_trans]


private def pageTwoBoundary (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ) :
    (classical.obj U.obj₃).Page 2 (s,t) ⟶ (classical.obj U.obj₁).Page 2 (s+1,t) :=
  (pageTwoIso U.obj₃ (s,t)).inv ≫ actualE2Boundary U hU hH t s ≫
    (pageTwoIso U.obj₁ (s+1,t)).hom

private def spectrumHomologyShortExactConnectingHom (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ) :
    (classical.obj U.obj₃).Page 2 (s,t) →+ (classical.obj U.obj₁).Page 2 (s+1,t) :=
  (pageTwoBoundary U hU hH s t).hom.toAddMonoidHom

private theorem pageTwoBoundary_square (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ) :
    actualE2Boundary U hU hH t s ≫ (pageTwoIso U.obj₁ (s+1,t)).hom =
      (pageTwoIso U.obj₃ (s,t)).hom ≫ pageTwoBoundary U hU hH s t := by
  simp only [pageTwoBoundary, Iso.hom_inv_id_assoc]

private theorem spectrumHomologyShortExactExactAtY (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ)
    (y : (classical.obj U.obj₂).Page 2 (s,t)) :
    (classical.map U.mor₂).pageMap 2 (s,t) y = 0 ↔
      ∃ x, (classical.map U.mor₁).pageMap 2 (s,t) x = y := by
  have h := range_eq_ker_of_iso _ _ _ _
    (pageTwoIso U.obj₁ (s,t)) (pageTwoIso U.obj₂ (s,t)) (pageTwoIso U.obj₃ (s,t))
    (pageTwoIso_natural U.mor₁ (s,t)) (pageTwoIso_natural U.mor₂ (s,t))
    (actualE2_range_eq_ker_middle U hU hH t s)
  change y ∈ LinearMap.ker _ ↔ y ∈ LinearMap.range _
  rw [h]

private theorem spectrumHomologyShortExactExactAtZ (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ)
    (z : (classical.obj U.obj₃).Page 2 (s,t)) :
    spectrumHomologyShortExactConnectingHom U hU hH s t z = 0 ↔
      ∃ y, (classical.map U.mor₂).pageMap 2 (s,t) y = z := by
  have h := range_eq_ker_of_iso _ _ _ _
    (pageTwoIso U.obj₂ (s,t)) (pageTwoIso U.obj₃ (s,t)) (pageTwoIso U.obj₁ (s+1,t))
    (pageTwoIso_natural U.mor₂ (s,t)) (pageTwoBoundary_square U hU hH s t)
    (actualE2_range_eq_ker_before_boundary U hU hH t s)
  change z ∈ LinearMap.ker (pageTwoBoundary U hU hH s t).hom ↔ z ∈ LinearMap.range _
  rw [h]

private theorem spectrumHomologyShortExactExactAtX (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ)
    (x : (classical.obj U.obj₁).Page 2 (s+1,t)) :
    (classical.map U.mor₁).pageMap 2 (s+1,t) x = 0 ↔
      ∃ z, spectrumHomologyShortExactConnectingHom U hU hH s t z = x := by
  have h := range_eq_ker_of_iso _ _ _ _
    (pageTwoIso U.obj₃ (s,t)) (pageTwoIso U.obj₁ (s+1,t)) (pageTwoIso U.obj₂ (s+1,t))
    (pageTwoBoundary_square U hU hH s t) (pageTwoIso_natural U.mor₁ (s+1,t))
    (actualE2_range_eq_ker_after_boundary U hU hH t s)
  change x ∈ LinearMap.ker _ ↔ x ∈ LinearMap.range (pageTwoBoundary U hU hH s t).hom
  rw [h]

private theorem spectrumHomologyShortExactLongExactSequence (U : Triangle Spectrum)
    (hU : U ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients U) (s t : ℤ) :
    (∀ y : (classical.obj U.obj₂).Page 2 (s,t),
      (classical.map U.mor₂).pageMap 2 (s,t) y = 0 ↔
        ∃ x, (classical.map U.mor₁).pageMap 2 (s,t) x = y) ∧
    (∀ z : (classical.obj U.obj₃).Page 2 (s,t),
      spectrumHomologyShortExactConnectingHom U hU hH s t z = 0 ↔
        ∃ y, (classical.map U.mor₂).pageMap 2 (s,t) y = z) ∧
    (∀ x : (classical.obj U.obj₁).Page 2 (s+1,t),
      (classical.map U.mor₁).pageMap 2 (s+1,t) x = 0 ↔
        ∃ z, spectrumHomologyShortExactConnectingHom U hU hH s t z = x) :=
  ⟨spectrumHomologyShortExactExactAtY U hU hH s t,
    spectrumHomologyShortExactExactAtZ U hU hH s t,
    spectrumHomologyShortExactExactAtX U hU hH s t⟩

end
end KIP126.Literature.Standard.ActualE2LES
end
