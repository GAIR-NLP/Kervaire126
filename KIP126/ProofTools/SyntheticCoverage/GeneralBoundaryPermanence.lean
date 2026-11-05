module

public import KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence

public import KIP126.ProofTools.Language

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence

/-! Absolute-boundary permanence for nonnegative first and second filtrations.
The shifted maps, their zero composite, and the first map's lambda-inversion
square give the geometric compatibility used in the boundary comparison.
The E2 operations come from these first quotients; denominators are the
ordinary Adams boundary submodules. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- The actual Q1 map expressed in the fixed native ordinary Adams E2
coordinates after shifting the source by the displayed weight. -/
@[no_expose] public def weightedFirstQuotientOperation (X Y : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (F : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (s t : ℤ) (x : Ambient background X (s,t)) : Ambient background Y (s+e,t+e) :=
  background.firstQuotient Y 0 (s+e) (t+e)
    (homotopyRegrade (by omega) (by omega)
      ((verticalTranslate _ e (t-s) t (nativeFirstLabel X s t x)≫
          (levelQuotientShiftIso X e 1).inv≫XModLambdaN.map F 1)≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1))

private theorem weighted_first_quotient_native_label (X Y : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (F : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (s t : ℤ) (x : Ambient background X (s,t)) :
    nativeFirstLabel Y (s+e) (t+e) (weightedFirstQuotientOperation X Y e F s t x)=
      homotopyRegrade (by omega) rfl
        (verticalTranslate _ e (t-s) t (nativeFirstLabel X s t x)≫
          (levelQuotientShiftIso X e 1).inv≫XModLambdaN.map F 1) := by
  rw [nativeFirstLabel_eq_regrade]
  simp only [weightedFirstQuotientOperation,LinearEquiv.symm_apply_apply,regrade_precomp,
    Category.assoc,←background.quotients.functoriality.map_comp,Iso.inv_hom_id_app]
  simp only [←Category.assoc,eqToHom_trans]
  erw [Category.comp_id]

private theorem weighted_full_source_first_label (X : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (s t : ℤ) (x : Ambient background X (s,t))
    (c : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (hc : c≫XModLambdaN.incl _ 1=nativeFirstLabel X s t x) :
    verticalTranslate _ e (t-s) t c≫XModLambdaN.incl _ 1=
      verticalTranslate _ e (t-s) t (nativeFirstLabel X s t x)≫(levelQuotientShiftIso X e 1).inv := by
  apply (cancel_mono (levelQuotientShiftIso X e 1).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [level_quotient_shift_incl,vertical_translate_comp,hc]

private theorem native_first_label_sub (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ)
    (a b : Ambient background X (s,t)) :
    nativeFirstLabel X s t (a-b)=nativeFirstLabel X s t a-nativeFirstLabel X s t b := by
  simp only [nativeFirstLabel,firstLabel_sub,Preadditive.sub_comp]

private def weightedAdjustedBoundary (Y : (AdamsObject (coefficients := background.coefficients))) (e : ℤ) (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
  homotopyRegrade (by omega) rfl
    ((positiveBoundarySourceIso e q (t-s) t).hom≫
      biSuspensionHomEquiv (t-s) t q (background.nu.functor.obj (Y.obj background.auxiliary))
        (z≫XModLambdaN.proj _ q))

private theorem weighted_adjusted_boundary_first (Y : (AdamsObject (coefficients := background.coefficients))) (e : ℤ) (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    weightedAdjustedBoundary Y e q s t z≫XModLambdaN.incl _ 1=
      boundaryRepresentative Y q s t z≫XModLambdaN.incl _ 1 := by
  simp only [weightedAdjustedBoundary,boundaryRepresentative,←regrade_comp,Category.assoc,
    sphere_automorphism_quotient_projection]

private theorem weighted_adjusted_boundary_torsion (Y : (AdamsObject (coefficients := background.coefficients))) (e : ℤ) (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    lambdaMultiply q (weightedAdjustedBoundary Y e q s t z)=0 := by
  dsimp only [weightedAdjustedBoundary]
  rw [lambda_regrade,lambda_torsion_precomp_sphere_iso _ _ q _ _
    (absolute_boundary_lambda_zero _ _ _ _ z)]
  exact regrade_zero _ _

private theorem weighted_adjusted_boundary_shift (Y : (AdamsObject (coefficients := background.coefficients))) (e : ℤ) (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    verticalTranslate _ e ((t+q)-(s+q+1)) (t+q) (weightedAdjustedBoundary Y e q s t z)=
      homotopyRegrade (by omega) (by omega)
        (biSuspensionHomEquiv (t-s) (t+e) q
          ((SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (Y.obj background.auxiliary)))
          ((verticalTranslate _ e (t-s) t z≫(levelQuotientShiftIso Y e q).inv)≫
            XModLambdaN.proj _ q)) := by
  dsimp only [weightedAdjustedBoundary]
  rw [vertical_translate_regrade,shifted_absolute_boundary_eq_precomp,
    normalized_homotopy_regrade_trans]

private def weightedBoundaryFiniteImage (Y Z : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (G : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    BiHom ((t+e)-(s+e)) (t+e) (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) q) :=
  homotopyRegrade (by omega) rfl
    (verticalTranslate _ e (t-s) t z≫(levelQuotientShiftIso Y e q).inv≫XModLambdaN.map G q)

private theorem weighted_boundary_finite_image_boundary (Y Z : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (G : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)) :
    boundaryRepresentative Z q (s+e) (t+e) (weightedBoundaryFiniteImage Y Z e G q s t z)=
      homotopyRegrade (by omega) (by omega)
        (verticalTranslate _ e ((t+q)-(s+q+1)) (t+q) (weightedAdjustedBoundary Y e q s t z)≫G) := by
  rw [weighted_adjusted_boundary_shift,regrade_comp,normalized_homotopy_regrade_trans]
  dsimp only [boundaryRepresentative,weightedBoundaryFiniteImage]
  rw [←regrade_comp,bi_susp_regrade,normalized_homotopy_regrade_trans]
  rw [Category.assoc,Category.assoc,XModLambdaN.proj_naturality]
  rw [←Category.assoc,←Category.assoc,bi_susp_natural background.quotients.coherence,regrade_comp]

private theorem weighted_boundary_finite_image_first (Y Z : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (G : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (a : Ambient background Y (s,t))
    (ha : z≫(background.quotients.tower _).rho 1 q hq=nativeFirstLabel Y s t a) :
    weightedBoundaryFiniteImage Y Z e G q s t z≫(background.quotients.tower _).rho 1 q hq=
      nativeFirstLabel Z (s+e) (t+e) (weightedFirstQuotientOperation Y Z e G s t a) := by
  have hsource : (verticalTranslate _ e (t-s) t z≫(levelQuotientShiftIso Y e q).inv)≫
      (background.quotients.tower _).rho 1 q hq=(verticalTranslate _ e (t-s) t (nativeFirstLabel Y s t a)≫(levelQuotientShiftIso Y e 1).inv) := by
    apply (cancel_mono (levelQuotientShiftIso Y e 1).hom).mp
    rw [Category.assoc,quotient_shift_restriction_on_spheres Y (0,e) 1 q
      (by decide) hq (levelQuotientShiftIso Y e 1) (levelQuotientShiftIso Y e q)
      (level_quotient_shift_incl Y e 1) (level_quotient_shift_incl Y e q)]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    rw [vertical_translate_comp,ha]
    simp only [Iso.inv_hom_id,Category.comp_id]
  dsimp only [weightedBoundaryFiniteImage]
  rw [←regrade_comp]
  simp only [Category.assoc]
  rw [←(background.quotients.natural G).rho_naturality]
  simp only [←Category.assoc]
  rw [hsource,weighted_first_quotient_native_label]
  simp only [Category.assoc]

private theorem weighted_adjusted_differential_correction
    (R : RealizationCoordinates background) (Y : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a : Ambient background Y (s,t)) (y : Ambient background Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a y)
    (image : BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (himage : image≫XModLambdaN.incl _ 1=nativeFirstLabel Y (s+q+1) (t+q) y) :
    ∃ z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q),
      z≫(background.quotients.tower _).rho 1 q hq=nativeFirstLabel Y s t a ∧
      ∃ b : BiHom ((t+q)-(s+q+1)) (t+q+1) (background.nu.functor.obj (Y.obj background.auxiliary)),
        homotopyRegrade rfl (by omega) (lambdaMultiply 1 b)=image-weightedAdjustedBoundary Y e q s t z ∧
        (R.sphere ((t+q)-(s+q+1)) (t+q+1)).hom≫background.recovery.realization.map b=
          (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫background.recovery.realization.map image := by
  obtain ⟨z,hz,hzy⟩ := (differential_iff_specified_adjacent_lift Y q hq s t a y).mp hd
  change boundaryRepresentative Y q s t z≫XModLambdaN.incl _ 1=
    nativeFirstLabel Y (s+q+1) (t+q) y at hzy
  let im : BiHom ((t+q)-(s+q+1)) ((t+q+1)-1) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    homotopyRegrade rfl (by omega) image
  let τ : BiHom ((t+q)-(s+q+1)) ((t+q+1)-1) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    homotopyRegrade rfl (by omega) (weightedAdjustedBoundary Y e q s t z)
  have hfirst : im≫XModLambdaN.incl _ 1=τ≫XModLambdaN.incl _ 1 := by
    dsimp only [im,τ]
    rw [←regrade_comp,←regrade_comp,weighted_adjusted_boundary_first,himage,hzy]
  have hτ : lambdaMultiply q τ=0 := by
    dsimp only [τ]
    rw [lambda_regrade,weighted_adjusted_boundary_torsion]
    exact regrade_zero _ _
  obtain ⟨b,hb,hreal⟩ := torsion_corrected_full_image R Y _ (t+q+1) q im τ hfirst hτ
  refine ⟨z,hz,b,?_,?_⟩
  · rw [hb]
    simp only [im,τ,regrade_precomp,Preadditive.comp_sub,←Category.assoc,
      eqToHom_trans,eqToHom_refl,Category.id_comp]
  · rw [hreal]
    have hh := realization_homotopy_regrade_full R rfl (by omega : t+q=(t+q+1)-1) image
    simpa only [im,eqToHom_refl,Category.id_comp] using hh

private theorem weighted_lambda_correction {A B : SyntheticSpectrum} (e : ℤ)
    (G : (SyntheticCategory.biShift (0,e)).obj A ⟶ B)
    (m w : ℤ) (image τ : BiHom m w A) (b : BiHom m (w+1) A)
    (hc : homotopyRegrade rfl (by omega) (lambdaMultiply 1 b)=image-τ)
    (hz : verticalTranslate A e m w image≫G=0) :
    homotopyRegrade rfl (by omega)
      (lambdaMultiply 1 (verticalTranslate A e m (w+1) b≫G))=
        -(verticalTranslate A e m w τ≫G) := by
  have hh := congrArg (fun z => verticalTranslate A e m w z≫G) hc
  rw [map_sub,Preadditive.sub_comp,hz,zero_sub] at hh
  rw [vertical_translate_regrade,←lambda_multiply_vertical_translate_comm A e 1 m (w+1) b,
    normalized_homotopy_regrade_trans,←regrade_comp] at hh
  simpa only [lambdaMultiply,Category.assoc] using hh

private theorem weighted_mapped_correction_adjacent_lift
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (G : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (image : BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (b : BiHom ((t+q)-(s+q+1)) (t+q+1) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (hc : homotopyRegrade rfl (by omega) (lambdaMultiply 1 b)=image-weightedAdjustedBoundary Y e q s t z)
    (hz : verticalTranslate _ e ((t+q)-(s+q+1)) (t+q) image≫G=0) :
    let bZ : BiHom (((t+e)+((q+1:ℕ):ℤ))-((s+e)+((q+1:ℕ):ℤ)+1)) ((t+e)+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Z.obj background.auxiliary)) :=
      homotopyRegrade (by omega) (by omega)
        (verticalTranslate _ e ((t+q)-(s+q+1)) (t+q+1) b≫G)
    ∃ eta : BiHom ((t+e)-(s+e)) (t+e) (XModLambdaN (background.nu.functor.obj (Z.obj background.auxiliary)) (q+1)),
      eta≫(background.quotients.tower _).rho 1 (q+1) (by omega)=
        weightedBoundaryFiniteImage Y Z e G q s t z≫(background.quotients.tower _).rho 1 q hq ∧
      lambdaMultiply 1 (bZ+boundaryRepresentative Z (q+1) (s+e) (t+e) eta)=0 := by
  dsimp only
  let zZ := weightedBoundaryFiniteImage Y Z e G q s t z
  let bZ : BiHom (((t+e)+((q+1:ℕ):ℤ))-((s+e)+((q+1:ℕ):ℤ)+1)) ((t+e)+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Z.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega)
      (verticalTranslate _ e ((t+q)-(s+q+1)) (t+q+1) b≫G)
  have heq : homotopyRegrade (by omega) (by omega) (lambdaMultiply 1 bZ)=
      (0 : BiHom (((t+e)+q)-((s+e)+q+1)) ((t+e)+q) _)-
        boundaryRepresentative Z q (s+e) (t+e) zZ := by
    have h := weighted_lambda_correction e G _ _ image (weightedAdjustedBoundary Y e q s t z) b hc hz
    have hh := congrArg (homotopyRegrade (by omega :
      (t+q)-(s+q+1)=((t+e)+q)-((s+e)+q+1)) (by omega : (t+q)+e=(t+e)+q)) h
    dsimp only [bZ,zZ]
    rw [lambda_regrade,normalized_homotopy_regrade_trans,zero_sub,
      weighted_boundary_finite_image_boundary]
    simpa only [normalized_homotopy_regrade_trans,regrade_precomp,Preadditive.comp_neg,
      ←Category.assoc,eqToHom_trans] using hh
  have hfirst : (0 : BiHom (((t+e)+q)-((s+e)+q+1)) ((t+e)+q) _)≫XModLambdaN.incl _ 1=
      boundaryRepresentative Z q (s+e) (t+e) zZ≫XModLambdaN.incl _ 1 := by
    have hh := congrArg (fun e => e≫XModLambdaN.incl _ 1) heq
    rw [←regrade_comp,lambdaMultiply_quotient_zero,regrade_zero,
      zero_sub,Preadditive.neg_comp] at hh
    rw [zero_comp]
    exact (neg_eq_zero.mp hh.symm).symm
  obtain ⟨eta,_,he,herr⟩ := mapped_correction_adjacent_lift Z Z (𝟙 _) q hq (s+e) (t+e)
    zZ 0 bZ hfirst (by simp) heq
  exact ⟨eta,by simpa only [background.quotients.functoriality.map_id,Category.comp_id] using he,
    by simpa only [Category.comp_id] using herr⟩

public def weightedBoundaryTargetOperation (Y Z : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (G : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ) (v : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))) :
    Ambient background Z ((s+e)+((q+1:ℕ):ℤ)+1,(t+e)+((q+1:ℕ):ℤ)) :=
  boundaryLabelRegrade (by omega) (by omega)
    (weightedFirstQuotientOperation Y Z e G _ _ v)

private theorem weighted_boundary_target_sub (Y Z : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (G : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (s t : ℤ) (v w : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))) :
    weightedBoundaryTargetOperation Y Z e G q s t (v-w)=
      weightedBoundaryTargetOperation Y Z e G q s t v-weightedBoundaryTargetOperation Y Z e G q s t w := by
  simp only [weightedBoundaryTargetOperation,weightedFirstQuotientOperation,native_first_label_sub,map_sub,
    Preadditive.sub_comp,regrade_precomp,Preadditive.comp_sub,boundary_label_regrade_sub]

/-- Full-image absolute-boundary permanence for a positive second map.
The first differential constructs a coordinate-corrected torsion class
with zero realization, so the final detector preserves the given full image. -/
private theorem weighted_second_boundary_lift_full_image
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (e : ℤ)
    (G : (SyntheticCategory.biShift (0,e)).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a : Ambient background Y (s,t)) (y : Ambient background Y (s+q+1,t+q))
    (v : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a y)
    (hd' : HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      ((q+1)+1) (s+e,t+e) ((s+e)+((q+1:ℕ):ℤ)+1,(t+e)+((q+1:ℕ):ℤ))
      (weightedFirstQuotientOperation Y Z e G s t a)
      (weightedBoundaryTargetOperation Y Z e G q s t v))
    (image : BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)))
    (himage : image≫XModLambdaN.incl _ 1=nativeFirstLabel Y (s+q+1) (t+q) y)
    (hzero : verticalTranslate _ e ((t+q)-(s+q+1)) (t+q) image≫G=0)
    (P : Submodule ℤ (Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))))
    (hP : permanentCycles background Y _ ≤ P) (hvP : v∈P)
    (hkernel : ∀ z, z∈P → weightedBoundaryTargetOperation Y Z e G q s t z ∈
      boundaries background Z (q+1) _ →
      IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) _ z) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) _ v ∧
      ClassicalDetects (background.classicalConvergence Y) _ v
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
          (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q)-(s+q+1)))≫
          (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
            background.recovery.realization.map image≫(hcomp.nu Y).target.hom) := by
  obtain ⟨z,hz,b,hb,hreal⟩ := weighted_adjusted_differential_correction R Y e q hq s t a y hd image himage
  obtain ⟨eta,heta,herr⟩ := weighted_mapped_correction_adjacent_lift Y Z e G q hq s t z image b hb hzero
  have heta' : eta≫(background.quotients.tower _).rho 1 (q+1) (by omega)=
      nativeFirstLabel Z (s+e) (t+e) (weightedFirstQuotientOperation Y Z e G s t a) :=
    heta.trans (weighted_boundary_finite_image_first Y Z e G q hq s t z a hz)
  let b' : BiHom ((t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)) (t+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Y.obj background.auxiliary)) := homotopyRegrade (by omega) (by omega) b
  let bZ : BiHom (((t+e)+((q+1:ℕ):ℤ))-((s+e)+((q+1:ℕ):ℤ)+1)) ((t+e)+((q+1:ℕ):ℤ))
      (background.nu.functor.obj (Z.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega)
      (verticalTranslate _ e ((t+q)-(s+q+1)) (t+q+1) b≫G)
  obtain ⟨w,hw,hwp,hwd⟩ := full_representative_first_label_detects R hcomp Y
    (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) b'
  have hbG : bZ≫XModLambdaN.incl _ 1=nativeFirstLabel Z _ _
      (weightedBoundaryTargetOperation Y Z e G q s t w) := by
    have h := weighted_full_source_first_label Y e (s+((q+1:ℕ):ℤ)+1) (t+((q+1:ℕ):ℤ)) w b' hw
    have hh := congrArg (fun u => u≫XModLambdaN.map G 1) h
    simp only [Category.assoc,←XModLambdaN.incl_naturality] at hh
    rw [weightedBoundaryTargetOperation,boundary_label_regrade_native,
      weighted_first_quotient_native_label,←hh]
    simp only [bZ,b',vertical_translate_regrade,normalized_homotopy_regrade_trans,regrade_comp,Category.assoc]
  have hdiff := adjacent_lambda_error_is_boundary Z q hq (s+e) (t+e) _ _ _ eta heta' bZ hbG herr hd'
  have hfinal : IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) _ (w-v) :=
    hkernel (w-v) (P.sub_mem (hP hwp) hvP) (by
      simpa only [weighted_boundary_target_sub] using hdiff)
  have htransport := realization_homotopy_regrade_full R
    (by omega : (t+q)-(s+q+1)=(t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1))
    (by omega : t+q+1=t+((q+1:ℕ):ℤ)) b
  rw [hreal] at htransport
  have htransport' := congrArg (fun e => e≫(hcomp.nu Y).target.hom) htransport
  simp only [Category.assoc] at htransport'
  have hdet := htransport' ▸ hwd
  exact classical_detects_of_final_boundary_difference Y _ w v _ hdet hfinal


/-- Absolute-boundary permanence for nonnegative first and second
filtrations. The normalized triangle gives the zero composite after
transport to positive source shifts; the realization square is
lambda-inversion compatibility for the first arrow. With `q=r−1`,
`boundaries (q+1)` is the denominator `B_<r+1`. -/
public theorem boundary_lift_prescribed_source_general
    (X Y Z : (AdamsObject (coefficients := background.coefficients))) (α β : ℕ)
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (F : (SyntheticCategory.biShift (0,(α:ℤ))).obj (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (G : (SyntheticCategory.biShift (0,(β:ℤ))).obj (background.nu.functor.obj (Y.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Z.obj background.auxiliary))
    (hfg : (SyntheticCategory.biShift (0,(β:ℤ))).map F≫G=0)
    (hF : background.recovery.realization.map F≫(KIP126.Literature.Standard.lambdaInversionAdamsComparison.nu Y).target.hom=
      (KIP126.Literature.Standard.lambdaInversionAdamsComparison.shiftedNu X α).target.hom≫f)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background X (s+q+1-α,t+q-α))
    (a : Ambient background Y (s,t))
    (v : Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ)))
    (hd : HasDifferential (background.classical.obj (Y.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) a
      (boundaryLabelRegrade (by omega) (by omega)
        (weightedFirstQuotientOperation X Y α F (s+q+1-α) (t+q-α) x)))
    (hd' : HasDifferential (background.classical.obj (Z.obj background.auxiliary))
      ((q+1)+1) (s+β,t+β) ((s+β)+((q+1:ℕ):ℤ)+1,(t+β)+((q+1:ℕ):ℤ))
      (weightedFirstQuotientOperation Y Z β G s t a)
      (weightedBoundaryTargetOperation Y Z β G q s t v))
    (P : Submodule ℤ (Ambient background Y (s+((q+1:ℕ):ℤ)+1,t+((q+1:ℕ):ℤ))))
    (hP : permanentCycles background Y _ ≤ P) (hvP : v∈P)
    (hkernel : ∀ z, z∈P → weightedBoundaryTargetOperation Y Z β G q s t z ∈
      boundaries background Z (q+1) _ →
      IsFinalBoundary (background.classical.obj (Y.obj background.auxiliary)) _ z)
    (ξ : HomotopyGroup ((t+q-α)-(s+q+1-α)) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s+q+1-α,t+q-α) x)
    (hξ : ClassicalDetects (background.classicalConvergence X) (s+q+1-α,t+q-α) x ξ) :
    IsPermanentCycle (background.classical.obj (Y.obj background.auxiliary)) _ v ∧
      ClassicalDetects (background.classicalConvergence Y) _ v
        (eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
          (t+((q+1:ℕ):ℤ))-(s+((q+1:ℕ):ℤ)+1)=(t+q-α)-(s+q+1-α)))≫ξ≫f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨c,hc,hreal⟩ := prescribed_native_source hcomp X (s+q+1-α) (t+q-α) x ξ hx hξ
  let c' := verticalTranslate _ (α:ℤ) ((t+q-α)-(s+q+1-α)) (t+q-α) c
  have hc' := weighted_full_source_first_label X α (s+q+1-α) (t+q-α) x c hc
  let image : BiHom ((t+q)-(s+q+1)) (t+q) (background.nu.functor.obj (Y.obj background.auxiliary)) :=
    homotopyRegrade (by omega) (by omega) (c'≫F)
  have hfirst : image≫XModLambdaN.incl _ 1=nativeFirstLabel Y (s+q+1) (t+q)
      (boundaryLabelRegrade (by omega) (by omega)
        (weightedFirstQuotientOperation X Y α F (s+q+1-α) (t+q-α) x)) := by
    rw [boundary_label_regrade_native,weighted_first_quotient_native_label,
      normalized_homotopy_regrade_trans]
    dsimp only [image]
    rw [←regrade_comp,Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hc']
    simp only [Category.assoc]
  have hzero : verticalTranslate _ (β:ℤ) ((t+q)-(s+q+1)) (t+q) image≫G=0 := by
    dsimp only [image]
    rw [vertical_translate_regrade,←regrade_comp,←vertical_translate_comp,Category.assoc,hfg,comp_zero]
    exact regrade_zero _ _
  obtain ⟨hvp,hvd⟩ := weighted_second_boundary_lift_full_image R hcomp Y Z β G q hq s t a _ v
    hd hd' image hfirst hzero P hP hvP hkernel
  have hrealc : (R.sphere ((t+q-α)-(s+q+1-α)) ((t+q-α)+α)).hom≫
      background.recovery.realization.map c'≫(hcomp.shiftedNu X α).target.hom=ξ :=
    (positive_source_realization_eq R hcomp X α _ _ c).trans hreal
  have hraw : (R.sphere ((t+q-α)-(s+q+1-α)) ((t+q-α)+α)).hom≫
      background.recovery.realization.map (c'≫F)≫(hcomp.nu Y).target.hom=ξ≫f := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [hF]
    simpa only [Category.assoc] using congrArg (fun e => e≫f) hrealc
  have hri := realization_homotopy_regrade_full R
    (by omega : (t+q-α)-(s+q+1-α)=(t+q)-(s+q+1))
    (by omega : (t+q-α)+α=t+q) (c'≫F)
  have hri' := congrArg (fun e => e≫(hcomp.nu Y).target.hom) hri
  simp only [Category.assoc] at hri'
  rw [hraw] at hri'
  have hi : (R.sphere ((t+q)-(s+q+1)) (t+q)).hom≫
      background.recovery.realization.map image≫(hcomp.nu Y).target.hom =
      eqToHom (congrArg (Sphere (C:=Spectrum)) (by omega :
        (t+q)-(s+q+1)=(t+q-α)-(s+q+1-α)))≫ξ≫f := hri'
  rw [hi] at hvd
  refine ⟨hvp,?_⟩
  simpa only [←Category.assoc,eqToHom_trans] using hvd

end
end KIP126.ProofTools.Internal.SyntheticCoverage
