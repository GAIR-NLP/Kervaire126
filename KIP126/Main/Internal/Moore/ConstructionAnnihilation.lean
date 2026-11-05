module

import all KIP126.Main.Internal.Moore.Construction
import all KIP126.Main.Internal.Moore.ConstructionTransport

/-! The actual Moore top-cell map and its normalized-triangle zero relation.
All object and suspension comparisons are retained explicitly. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum Spectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

private def mooreTopImage
    (c : BiHom 124 132 (XModLambdaN
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4)) :
    BiHom 123 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4) :=
  (susp_invariance 123 131 1 1 _).symm
    (c ≫ XModLambdaN.map (background.nu.functor.map
      KIP126.AdamsComputation.Moore.top) 4 ≫ (mooreNuSuspensionQuotientIso 4).hom)

private def mooreNormalizedTriangle : Triangle SyntheticSpectrum :=
  normalizedTriangle background KIP126.AdamsComputation.Moore.triangle moore_exponent_sum

private theorem moore_normalized_top_composite_zero :
    mooreNormalizedTriangle.mor₃ ≫
      (shiftFunctor SyntheticSpectrum (1 : ℤ)).map mooreNormalizedTriangle.mor₁ = 0 :=
  comp_distTriang_mor_zero₃₁ _ moore_normalized_triangle_distinguished

private theorem moore_normalized_top_quotient_composite_zero (q : ℕ) (hq : 0 < q) :
    XModLambdaN.map mooreNormalizedTriangle.mor₃ q ≫
      XModLambdaN.map
        ((shiftFunctor SyntheticSpectrum (1 : ℤ)).map mooreNormalizedTriangle.mor₁) q = 0 := by
  obtain ⟨e, _, hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    KIP126.AdamsComputation.Moore.triangle moore_exponent_sum q hq
  apply (cancel_mono e.hom).mp
  have hz := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map mooreNormalizedTriangle.mor₃ q ≫ (-(_ ≫ e.hom)) = 0 at hz
  rw [Preadditive.comp_neg, neg_eq_zero] at hz
  simpa only [mooreNormalizedTriangle, Category.assoc, zero_comp] using hz

private theorem negative_lift_at_zero {A B : SyntheticSpectrum} {k : ℕ}
    (hk : k = 0) (M : (SyntheticCategory.biShift (0, (k : ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hM : lambdaToPositivePow k A ≫ M = g) :
    negativeLift k M = g ≫ SyntheticCategory.biShift_zero.inv.app B ≫
      eqToHom (congrArg (fun j : ℕ =>
        (SyntheticCategory.biShift (0, -(j : ℤ))).obj B) hk).symm := by
  subst k
  simp only [eqToHom_refl, Category.comp_id]
  apply ((SyntheticCategory.biShift_zero.app B).eq_comp_inv).mpr
  have hn : negativeLift 0 M ≫ lambdaPow 0 B = lambdaToPositivePow 0 A ≫ M := by
    simp only [negativeLift, lambdaToPositivePow, Category.assoc]
    rw [lambdaPow_naturality]
  exact hn.trans hM

private def zeroNegativeIso (A : SyntheticSpectrum) (k : ℕ) (hk : k = 0) :
    (SyntheticCategory.biShift (0, -(k : ℤ))).obj A ≅ A :=
  eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0, -(j : ℤ))).obj A) hk) ≪≫
    SyntheticCategory.biShift_zero.app A

private def onePositiveIso (A : SyntheticSpectrum) (k : ℕ) (hk : k = 1) :
    (SyntheticCategory.biShift (0, (k : ℤ))).obj A ≅
      (SyntheticCategory.biShift (0, 1)).obj A :=
  eqToIso (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0, (j : ℤ))).obj A) hk)

private def rawNormalizedConnecting {A C D : SyntheticSpectrum} (ef eg eh : ℕ)
    (he : (ef : ℤ) + eg + eh = 1)
    (h : (SyntheticCategory.biShift (0, (eh : ℤ))).obj C ⟶ D)
    (σ : D ≅ (SyntheticCategory.biShift (1, 1)).obj A) :
    (SyntheticCategory.biShift (0, -(eg : ℤ))).obj C ⟶
      ((SyntheticCategory.biShift (0, (ef : ℤ))).obj A)⟦(1 : ℤ)⟧ :=
  (SyntheticCategory.biShift (0, -(eg : ℤ))).map (negativeLift eh h) ≫
    (SyntheticCategory.biShift (0, -(eg : ℤ))).map
      ((SyntheticCategory.biShift (0, -(eh : ℤ))).map σ.hom) ≫
    (SyntheticCategory.biShift (0, -(eg : ℤ))).map
      ((SyntheticCategory.biShift_comp (1, 1) (0, -(eh : ℤ))).hom.app A) ≫
    (SyntheticCategory.biShift_comp ((1, 1) + (0, -(eh : ℤ))) (0, -(eg : ℤ))).hom.app A ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj A)
      (show ((1, 1) + (0, -(eh : ℤ))) + (0, -(eg : ℤ)) = (0, (ef : ℤ)) + (1, 0) from by
        ext
        · rfl
        · dsimp
          omega)) ≫
    (SyntheticCategory.biShift_comp (0, (ef : ℤ)) (1, 0)).inv.app A ≫
    (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).hom.app _

private theorem raw_connecting_one_zero_zero {A C D : SyntheticSpectrum}
    (ef eg eh : ℕ) (he : (ef : ℤ) + eg + eh = 1)
    (hf : ef = 1) (hg : eg = 0) (hh : eh = 0)
    (h : (SyntheticCategory.biShift (0, (eh : ℤ))).obj C ⟶ D)
    (g : C ⟶ D) (hhg : lambdaToPositivePow eh C ≫ h = g)
    (σ : D ≅ (SyntheticCategory.biShift (1, 1)).obj A) :
    rawNormalizedConnecting ef eg eh he h σ ≫
      (shiftFunctor SyntheticSpectrum (1 : ℤ)).map (onePositiveIso A ef hf).hom =
    (zeroNegativeIso C eg hg).hom ≫ g ≫ σ.hom ≫
      (SyntheticCategory.biShift_comp (0, 1) (1, 0)).inv.app A ≫
      (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).hom.app _ := by
  subst ef; subst eg; subst eh
  dsimp only [rawNormalizedConnecting, onePositiveIso, zeroNegativeIso]
  simp only [eqToHom_refl, eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Category.id_comp]
  rw [negative_lift_at_zero rfl h g hhg]
  simp only [eqToHom_refl, Category.comp_id, Functor.map_comp, Category.assoc]
  have hr := background.quotients.coherence.right_unit (1, 1) A
  simp only [biShiftAddIso, eqToIso_refl, Iso.trans_refl] at hr
  erw [hr]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  simp only [Functor.id_map, Iso.app_hom]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  simp only [Functor.id_map]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  simp only [Functor.id_map, Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]
  rfl

private def mooreNormalizedSourceIso : mooreNormalizedTriangle.obj₃ ≅
    background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum :=
  zeroNegativeIso _ _ moore_cell_exponents.1

private def mooreNormalizedFirstIso : mooreNormalizedTriangle.obj₁ ≅
    (SyntheticCategory.biShift (0, 1)).obj (background.nu.functor.obj SphereSpectrum) :=
  onePositiveIso _ _ twoMap_exponent

private def mooreTopLandingIso :
    background.nu.functor.obj ((shiftFunctor Spectrum (1 : ℤ)).obj SphereSpectrum) ≅
      ((SyntheticCategory.biShift (0, 1)).obj
        (background.nu.functor.obj SphereSpectrum))⟦(1 : ℤ)⟧ :=
  background.nu.suspensionIso SphereSpectrum ≪≫
    ((SyntheticCategory.biShift_comp (0, 1) (1, 0)).app _).symm ≪≫
    (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).app _

private theorem moore_normalized_connecting_square :
    mooreNormalizedTriangle.mor₃ ≫
      (shiftFunctor SyntheticSpectrum (1 : ℤ)).map mooreNormalizedFirstIso.hom =
    mooreNormalizedSourceIso.hom ≫
      background.nu.functor.map KIP126.AdamsComputation.Moore.top ≫ mooreTopLandingIso.hom := by
  have h := raw_connecting_one_zero_zero _ _ _ moore_exponent_sum
    twoMap_exponent moore_cell_exponents.1 moore_cell_exponents.2
    (background.normalizedMap KIP126.AdamsComputation.Moore.adamsObject (.shift 1 .sphere)
      KIP126.AdamsComputation.Moore.top).map
    (background.nu.functor.map KIP126.AdamsComputation.Moore.top)
    (background.normalizedMap KIP126.AdamsComputation.Moore.adamsObject (.shift 1 .sphere)
      KIP126.AdamsComputation.Moore.top).factorization
    (background.nu.suspensionIso SphereSpectrum)
  simpa only [mooreNormalizedTriangle, normalizedTriangle, normalizedConnecting,
    rawNormalizedConnecting, mooreNormalizedFirstIso, mooreNormalizedSourceIso,
    mooreTopLandingIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, Triangle.mk_mor₃, KIP126.AdamsComputation.Moore.triangle,
    AdamsObject.obj, ClassicalObject.obj, Triangle.mk_obj₃,
    KIP126.AdamsComputation.Moore.adamsObject] using h

private theorem moore_normalized_first_h0 :
    mooreNormalizedFirstIso.inv ≫ mooreNormalizedTriangle.mor₁ = h0NormalizedMap := by
  exact selectedTwoNormalized_eq_h0

private theorem moore_actual_top_shift_h0_zero :
    background.nu.functor.map KIP126.AdamsComputation.Moore.top ≫
      mooreTopLandingIso.hom ≫ (shiftFunctor SyntheticSpectrum (1 : ℤ)).map h0NormalizedMap = 0 := by
  apply (cancel_epi mooreNormalizedSourceIso.hom).mp
  rw [←reassoc_of% moore_normalized_connecting_square]
  simp only [comp_zero]
  rw [←CategoryTheory.Functor.map_comp, ←moore_normalized_first_h0, Iso.hom_inv_id_assoc]
  exact moore_normalized_top_composite_zero

private theorem moore_actual_top_quotient_shift_h0_zero (q : ℕ) (hq : 0 < q) :
    XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) q ≫
      XModLambdaN.map mooreTopLandingIso.hom q ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1 : ℤ)).map h0NormalizedMap) q = 0 := by
  let Q := background.quotients.functoriality.functor q
  let e := Q.mapIso mooreNormalizedSourceIso
  apply (cancel_epi e.hom).mp
  change Q.map mooreNormalizedSourceIso.hom ≫ Q.map _ ≫ Q.map _ ≫ Q.map _ = _
  simp only [←Q.map_comp, comp_zero]
  rw [←reassoc_of% moore_normalized_connecting_square]
  rw [←CategoryTheory.Functor.map_comp, ←moore_normalized_first_h0, Iso.hom_inv_id_assoc]
  rw [Q.map_comp]
  exact moore_normalized_top_quotient_composite_zero q hq

private theorem moore_fourth_top_quotient_shift_h0_zero
    (c : BiHom 124 132 (XModLambdaN
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4)) :
    c ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4 ≫
      XModLambdaN.map mooreTopLandingIso.hom 4 ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1 : ℤ)).map h0NormalizedMap) 4 = 0 := by
  rw [moore_actual_top_quotient_shift_h0_zero 4 (by decide), comp_zero]

private def mooreSuspendedUnitIso :
    (background.nu.functor.obj (SphereSpectrum (C := Spectrum)))⟦(1 : ℤ)⟧ ≅
      Smn (Syn := SyntheticSpectrum) 1 0 :=
  ((SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).app _).symm ≪≫
    (SyntheticCategory.biShift (1, 0)).mapIso background.nu.unitIso

private def mooreShiftedH0 : Smn (Syn := SyntheticSpectrum) 1 1 ⟶ Smn 1 0 :=
  (SyntheticCategory.biShift_comp (0, 1) (1, 0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
    (SyntheticCategory.biShift (1, 0)).map KIP126.Literature.Standard.syntheticH0

private theorem moore_top_landing_h0_square :
    mooreTopLandingIso.hom ≫ (shiftFunctor SyntheticSpectrum (1 : ℤ)).map h0NormalizedMap ≫
      mooreSuspendedUnitIso.hom = mooreNuSuspensionIso.hom ≫ mooreShiftedH0 := by
  dsimp only [mooreTopLandingIso, mooreSuspendedUnitIso, mooreNuSuspensionIso,
    mooreShiftedH0, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [←reassoc_of% ((SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).hom.naturality
    h0NormalizedMap)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [←CategoryTheory.Functor.map_comp]
  simp only [h0NormalizedMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [CategoryTheory.Functor.map_comp]
  erw [←reassoc_of% ((SyntheticCategory.biShift_comp (0, 1) (1, 0)).inv.naturality
    background.nu.unitIso.hom)]
  rfl

private theorem moore_actual_top_sphere_quotient_h0_zero (q : ℕ) (hq : 0 < q) :
    XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) q ≫
      XModLambdaN.map mooreNuSuspensionIso.hom q ≫ XModLambdaN.map mooreShiftedH0 q = 0 := by
  have h := congrArg (fun f => f ≫ XModLambdaN.map mooreSuspendedUnitIso.hom q)
    (moore_actual_top_quotient_shift_h0_zero q hq)
  simp only [Category.assoc, zero_comp] at h
  rw [←background.quotients.functoriality.map_comp,
    ←background.quotients.functoriality.map_comp, moore_top_landing_h0_square,
    background.quotients.functoriality.map_comp] at h
  exact h

private theorem moore_fourth_top_sphere_quotient_h0_zero
    (c : BiHom 124 132 (XModLambdaN
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4)) :
    c ≫ XModLambdaN.map (background.nu.functor.map KIP126.AdamsComputation.Moore.top) 4 ≫
      XModLambdaN.map mooreNuSuspensionIso.hom 4 ≫ XModLambdaN.map mooreShiftedH0 4 = 0 := by
  rw [moore_actual_top_sphere_quotient_h0_zero 4 (by decide), comp_zero]

/-- The same desuspended top image is killed by the quotient of the
suspended h₀ map. Identifying this postcomposition with sphereAction
requires compatibility of the two actions. -/
private theorem moore_top_image_actual_h0_zero
    (c : BiHom 124 132 (XModLambdaN
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4)) :
    susp_invariance 123 131 1 1 (XModLambdaN (S_0_0 : SyntheticSpectrum) 4)
        (mooreTopImage c) ≫
      (sphereQuotientShiftIso (1, 1) 4).hom ≫ XModLambdaN.map mooreShiftedH0 4 = 0 := by
  dsimp only [mooreTopImage]
  rw [Equiv.apply_symm_apply]
  simp only [mooreNuSuspensionQuotientIso, quotientAlongSphereShift, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact moore_fourth_top_sphere_quotient_h0_zero c


end
end KIP126.Main.Internal.Moore
