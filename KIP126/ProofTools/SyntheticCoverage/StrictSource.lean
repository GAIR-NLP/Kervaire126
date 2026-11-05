module

import all KIP126.ProofTools.SyntheticCoverage.FullImage
import all KIP126.ProofTools.SyntheticCoverage.SourceShift
import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSource

/-! Prescribed classical sources for the synthetic coverage arguments.
The realization coordinates are the selected coordinates of the specified
prescribed-lift theorem. The comparison uses those same coordinates. -/

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

private theorem regrade_zero {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') :
    homotopyRegrade hm hw (0 : BiHom m w A) = 0 := by
  subst m'; subst w'; rfl

private theorem realization_homotopy_regrade_full
    (R : RealizationCoordinates background) {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    (R.sphere m' w').hom ≫ background.recovery.realization.map (homotopyRegrade hm hw a) =
      eqToHom (congrArg (Sphere (C := Spectrum)) hm.symm) ≫
        (R.sphere m w).hom ≫ background.recovery.realization.map a := by
  subst m'; subst w'
  simp only [homotopyRegrade,eqToHom_refl,Category.id_comp]

/-- The prescribed-lift comparison preserves the specified classical
class after removing the zero shift. -/
private theorem prescribed_native_source
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ) (x : Ambient background X (s,t))
    (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence X) (s,t) x a) :
    ∃ b : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x ∧
      (KIP126.Literature.Standard.realizationData.sphere (t-s) t).hom ≫
        background.recovery.realization.map b ≫ (hcomp.nu X).target.hom = a := by
  obtain ⟨b,hb,hreal⟩ := KIP126.Literature.Standard.realization_prescribed_lift
    X s t x a hx ha
  refine ⟨b ≫ SyntheticCategory.biShift_zero.hom.app _,?_,?_⟩
  · change (b ≫ SyntheticCategory.biShift_zero.hom.app _) ≫ XModLambdaN.incl _ 1 = _
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
    change quotientClass 1 b ≫ XModLambdaN.map _ 1 = _
    rw [hb]
    rfl
  · rw [Functor.map_comp,hcomp.nu_target]
    simpa only [KIP126.Literature.Standard.realizeNu,realizeNuZero,Category.assoc] using hreal

/-- Zero of the actual ordinary first operation gives zero of the first
quotient of every full source with that prescribed native first label. -/
private theorem ordinary_full_image_first_quotient_zero
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s,t))
    (b : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (hb : b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x)
    (hfx : (background.classical.map f).pageMap 2 (s,t) x = 0) :
    (b ≫ background.nu.functor.map f) ≫ XModLambdaN.incl _ 1 = 0 := by
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hb,
    native_first_label_natural,hfx]
  unfold nativeFirstLabel
  have hz : firstLabel background Y s t 0 = 0 := by
    simpa only [sub_self] using firstLabel_sub Y s t 0 0
  rw [hz,zero_comp]

/-- The ordinary-map source bridge supplies the actual full source and
zero first quotient of its image while retaining the prescribed classical
source. This consumes only the original strict source and first-operation
zero hypotheses, with the fixed common realization comparison. -/
private theorem prescribed_ordinary_source_zero_image
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s,t))
    (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence X) (s,t) x a)
    (hfx : (background.classical.map f).pageMap 2 (s,t) x = 0) :
    ∃ b : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x ∧
      (KIP126.Literature.Standard.realizationData.sphere (t-s) t).hom ≫
        background.recovery.realization.map b ≫ (hcomp.nu X).target.hom = a ∧
      (b ≫ background.nu.functor.map f) ≫ XModLambdaN.incl _ 1 = 0 := by
  obtain ⟨b,hb,hreal⟩ := prescribed_native_source hcomp X s t x a hx ha
  exact ⟨b,hb,hreal,ordinary_full_image_first_quotient_zero X Y f s t x b hb hfx⟩

/-- The ordinary-map branch constructs a permanent first label of the
image of every specified strict source. This is before comparison with the
candidate supplied by the two-layer zigzag. -/
private theorem prescribed_ordinary_image_first_label
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (x : Ambient background X (s,t))
    (a : HomotopyGroup (t-s) (X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence X) (s,t) x a)
    (hfx : (background.classical.map f).pageMap 2 (s,t) x = 0) :
    ∃ c : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      c ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x ∧
      ∃ b : BiHom ((t+1)-(s+1)) (t+1) (background.nu.functor.obj (Y.obj background.auxiliary)),
        lambdaMultiply 1 b = homotopyRegrade (by omega) (by omega)
          (c ≫ background.nu.functor.map f) ∧
        ∃ w : Ambient background Y (s+1,t+1),
          b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel Y (s+1) (t+1) w ∧
          w ∈ permanentCycles background Y (s+1,t+1) ∧
          ClassicalDetects (background.classicalConvergence Y) (s+1,t+1) w
            (eqToHom (congrArg (Sphere (C := Spectrum))
              (show (t+1)-(s+1)=t-s by omega)) ≫ a ≫ f) := by
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨c,hc,hreal,hzero⟩ := prescribed_ordinary_source_zero_image hcomp X Y f s t x a hx ha hfx
  have hm : t-s=(t+1)-(s+1) := by omega
  let c' : BiHom ((t+1)-(s+1)) ((t+1)-1)
      (background.nu.functor.obj (X.obj background.auxiliary)) :=
    homotopyRegrade hm (by omega) c
  have hz : (c' ≫ background.nu.functor.map f) ≫ XModLambdaN.incl _ 1 = 0 := by
    dsimp only [c']
    rw [←regrade_comp,←regrade_comp,hzero]
    exact regrade_zero _ _
  obtain ⟨b,hb,w,hw,hp,hclass⟩ := full_image_first_label_detects R hcomp _ Y
    (background.nu.functor.map f) (s+1) (t+1) c' hz
  refine ⟨c,hc,b,?_,w,hw,hp,?_⟩
  · simpa only [c',regrade_comp] using hb
  · have himage : (R.sphere ((t+1)-(s+1)) ((t+1)-1)).hom ≫
        background.recovery.realization.map (c' ≫ background.nu.functor.map f) ≫
          (hcomp.nu Y).target.hom =
        eqToHom (congrArg (Sphere (C := Spectrum)) hm.symm) ≫ a ≫ f := by
      have hreal' : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map
          (c ≫ background.nu.functor.map f) ≫ (hcomp.nu Y).target.hom = a ≫ f := by
        rw [Functor.map_comp,hcomp.nu_target]
        have hn := background.recovery.nuRealizationIso.hom.naturality f
        dsimp only [Functor.comp_map,Functor.id_map] at hn
        simp only [Category.assoc]
        rw [hn]
        rw [←hcomp.nu_target X]
        simpa only [Category.assoc] using congrArg (fun z => z ≫ f) hreal
      have htransport := realization_homotopy_regrade_full R
        hm (show t=(t+1)-1 by omega) (c ≫ background.nu.functor.map f)
      have ht := congrArg (fun z => z ≫ (hcomp.nu Y).target.hom) htransport
      simp only [Category.assoc] at ht
      rw [hreal'] at ht
      simpa only [c',regrade_comp] using ht
    exact himage ▸ hclass

/-- The actual positive shift of a specified native full source has the
prescribed positive first-quotient label. -/
private theorem positive_full_source_first_label
    (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ) (x : Ambient background X (s,t))
    (c : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (hc : c ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x) :
    verticalTranslate _ 1 (t-s) t c ≫ XModLambdaN.incl _ 1 =
      (background.firstQuotient X 1 s t).symm x := by
  rw [←positive_first_label_shift X s t x]
  apply (cancel_mono (levelQuotientShiftIso X 1 1).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [level_quotient_shift_incl,vertical_translate_comp,hc]

private theorem homotopy_regrade_eq_zero {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm hw a = 0 ↔ a = 0 := by
  subst m'; subst w'; rfl

/-- Zero of the positive first operation implies zero of the same actual
full image in the first quotient. The positive map is retained literally. -/
private theorem positive_full_image_first_quotient_zero
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (F : (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
        background.nu.functor.obj (Y.obj background.auxiliary))
    (s t : ℤ) (x : Ambient background X (s,t))
    (c : BiHom (t-s) (t+1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))))
    (hc : c ≫ XModLambdaN.incl _ 1 = (background.firstQuotient X 1 s t).symm x)
    (hfx : positiveFirstQuotientOperation X Y F s t x = 0) :
    (c ≫ F) ≫ XModLambdaN.incl _ 1 = 0 := by
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hc]
  have h := positive_first_quotient_native_label X Y F s t x
  rw [hfx] at h
  have hz : nativeFirstLabel Y (s+1) (t+1) 0 = 0 := by
    unfold nativeFirstLabel
    have hh : firstLabel background Y (s+1) (t+1) 0 = 0 := by
      simpa only [sub_self] using firstLabel_sub Y (s+1) (t+1) 0 0
    rw [hh,zero_comp]
  rw [hz] at h
  exact (homotopy_regrade_eq_zero _ _ _).mp h.symm

/-- The positive normalization of the first arrow has the same realized
classical map, with the matching shifted source comparison. -/
private theorem normalized_positive_realization_square
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    background.recovery.realization.map (normalizedFirstMap T hf) ≫ (hcomp.nu T.Y).target.hom =
      (hcomp.shiftedNu T.X 1).target.hom ≫ T.f := by
  have h := KIP126.ProofTools.Paper.normalized_realization_square background R hcomp T.X T.Y T.f
  have transport (k : ℕ) (hk : k=1)
      (F : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (background.nu.functor.obj (T.X.obj background.auxiliary)) ⟶
          background.nu.functor.obj (T.Y.obj background.auxiliary))
      (hF : background.recovery.realization.map F ≫ (hcomp.nu T.Y).target.hom =
        (hcomp.shiftedNu T.X k).target.hom ≫ T.f) :
      background.recovery.realization.map
        ((congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj
          (background.nu.functor.obj (T.X.obj background.auxiliary)) ⟶
            background.nu.functor.obj (T.Y.obj background.auxiliary)) hk).mp F) ≫ (hcomp.nu T.Y).target.hom =
          (hcomp.shiftedNu T.X 1).target.hom ≫ T.f := by
    subst k
    exact hF
  exact transport _ hf (background.normalizedMap T.X T.Y T.f).map h

/-- The original positive first-arrow equation gives zero first quotient
of the actual normalized full image. -/
private theorem normalized_positive_image_first_quotient_zero
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t))
    (c : BiHom (t-s) (t+1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))))
    (hc : c ≫ XModLambdaN.incl _ 1 = (background.firstQuotient T.X 1 s t).symm x)
    (hfx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0) :
    (c ≫ normalizedFirstMap T hf) ≫ XModLambdaN.incl _ 1 = 0 := by
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hc]
  have h := cofiberFirstQuotientBoundary_native_label T hf s t x
  rw [hfx] at h
  have hz : nativeFirstLabel T.Y (s+1) (t+1) 0 = 0 := by
    unfold nativeFirstLabel
    have hh : firstLabel background T.Y (s+1) (t+1) 0 = 0 := by
      simpa only [sub_self] using firstLabel_sub T.Y (s+1) (t+1) 0 0
    rw [hh,zero_comp]
  rw [hz] at h
  exact (homotopy_regrade_eq_zero _ _ _).mp h.symm

/-- Positive weight transport preserves the realized source through
lambda coherence and the matching shifted comparison. -/
private theorem positive_source_realization_eq
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (X : (AdamsObject (coefficients := background.coefficients))) (k : ℕ) (m w : ℤ)
    (a : BiHom m w (background.nu.functor.obj (X.obj background.auxiliary))) :
    (R.sphere m (w+(k:ℤ))).hom ≫
        background.recovery.realization.map (verticalTranslate _ (k:ℤ) m w a) ≫
          (hcomp.shiftedNu X k).target.hom =
      (R.sphere m w).hom ≫ background.recovery.realization.map a ≫ (hcomp.nu X).target.hom := by
  let b := verticalTranslate _ (k:ℤ) m w a
  have hshift := lambda_multiply_vertical_translate _ k m w a
  have hr := realization_homotopy_regrade_full R rfl
    (show (w+(k:ℤ))-(k:ℤ)=w by omega) (lambdaMultiply k b)
  rw [eqToHom_refl,Category.id_comp] at hr
  change (R.sphere m w).hom ≫ background.recovery.realization.map
    (homotopyRegrade rfl _ (lambdaMultiply k b)) = _ at hr
  rw [hshift,realization_lambda_multiply R m (w+(k:ℤ)) k b] at hr
  have hh := congrArg (fun z => z ≫ (hcomp.shiftedNu X k).target.hom) hr
  simp only [Functor.map_comp,Category.assoc,hcomp.shiftedNu_target] at hh
  exact hh.symm

/-- Every prescribed strict classical source has an actual positively
shifted full lift with the exact prescribed first label and exact original
realization. The first positive operation zero condition then annihilates
the first quotient of its actual normalized image. -/
private theorem prescribed_positive_source_zero_image
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t))
    (a : HomotopyGroup (t-s) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s,t) x a)
    (hfx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0) :
    ∃ c : BiHom (t-s) (t+1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))),
      c ≫ XModLambdaN.incl _ 1 = (background.firstQuotient T.X 1 s t).symm x ∧
      (KIP126.Literature.Standard.realizationData.sphere (t-s) (t+1)).hom ≫
        background.recovery.realization.map c ≫ (hcomp.shiftedNu T.X 1).target.hom = a ∧
      (c ≫ normalizedFirstMap T hf) ≫ XModLambdaN.incl _ 1 = 0 := by
  obtain ⟨b,hb,hreal⟩ := prescribed_native_source hcomp T.X s t x a hx ha
  let c := verticalTranslate _ 1 (t-s) t b
  have hc := positive_full_source_first_label T.X s t x b hb
  refine ⟨c,hc,?_,normalized_positive_image_first_quotient_zero T hf s t x c hc hfx⟩
  exact (positive_source_realization_eq KIP126.Literature.Standard.realizationData
    hcomp T.X 1 (t-s) t b).trans hreal

/-- The positive-first-arrow branch retains every specified strict
classical source through the full lift, actual lambda division, and final
classical image comparison. The later candidate comparison remains a
separate two-layer argument. -/
private theorem prescribed_positive_image_first_label
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t))
    (a : HomotopyGroup (t-s) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s,t) x a)
    (hfx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0) :
    ∃ c : BiHom (t-s) (t+1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))),
      c ≫ XModLambdaN.incl _ 1 = (background.firstQuotient T.X 1 s t).symm x ∧
      ∃ b : BiHom ((t+2)-(s+2)) (t+2) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
        lambdaMultiply 1 b = homotopyRegrade (by omega) (by omega)
          (c ≫ normalizedFirstMap T hf) ∧
        ∃ w : Ambient background T.Y (s+2,t+2),
          b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.Y (s+2) (t+2) w ∧
          w ∈ permanentCycles background T.Y (s+2,t+2) ∧
          ClassicalDetects (background.classicalConvergence T.Y) (s+2,t+2) w
            (eqToHom (congrArg (Sphere (C := Spectrum))
              (show (t+2)-(s+2)=t-s by omega)) ≫ a ≫ T.f) := by
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨c,hc,hreal,hzero⟩ := prescribed_positive_source_zero_image hcomp T hf s t x a hx ha hfx
  have hm : t-s=(t+2)-(s+2) := by omega
  let c' : BiHom ((t+2)-(s+2)) ((t+2)-1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) :=
    homotopyRegrade hm (by omega) c
  have hz : (c' ≫ normalizedFirstMap T hf) ≫ XModLambdaN.incl _ 1 = 0 := by
    dsimp only [c']
    rw [←regrade_comp,←regrade_comp,hzero]
    exact regrade_zero _ _
  obtain ⟨b,hb,w,hw,hp,hclass⟩ := full_image_first_label_detects R hcomp _ T.Y
    (normalizedFirstMap T hf) (s+2) (t+2) c' hz
  refine ⟨c,hc,b,?_,w,hw,hp,?_⟩
  · simpa only [c',regrade_comp] using hb
  · have himage : (R.sphere ((t+2)-(s+2)) ((t+2)-1)).hom ≫
        background.recovery.realization.map (c' ≫ normalizedFirstMap T hf) ≫
          (hcomp.nu T.Y).target.hom =
        eqToHom (congrArg (Sphere (C := Spectrum)) hm.symm) ≫ a ≫ T.f := by
      have hreal' : (R.sphere (t-s) (t+1)).hom ≫ background.recovery.realization.map
          (c ≫ normalizedFirstMap T hf) ≫ (hcomp.nu T.Y).target.hom = a ≫ T.f := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
        rw [normalized_positive_realization_square R hcomp T hf]
        simpa only [Category.assoc] using congrArg (fun z => z ≫ T.f) hreal
      have htransport := realization_homotopy_regrade_full R
        hm (show t+1=(t+2)-1 by omega) (c ≫ normalizedFirstMap T hf)
      have ht := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) htransport
      simp only [Category.assoc] at ht
      rw [hreal'] at ht
      simpa only [c',regrade_comp] using ht
    exact himage ▸ hclass

/-- The same strict-image theorem in successive-step bidegree coordinates. -/
private theorem prescribed_positive_image_first_label_successive
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t))
    (a : HomotopyGroup (t-s) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s,t) x a)
    (hfx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0) :
    ∃ c : BiHom (t-s) (t+1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))),
      c ≫ XModLambdaN.incl _ 1 = (background.firstQuotient T.X 1 s t).symm x ∧
      ∃ b : BiHom ((t+1+1)-(s+1+1)) (t+1+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)),
        lambdaMultiply 1 b = homotopyRegrade (by omega) (by omega)
          (c ≫ normalizedFirstMap T hf) ∧
        ∃ w : Ambient background T.Y (s+1+1,t+1+1),
          b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.Y (s+1+1) (t+1+1) w ∧
          w ∈ permanentCycles background T.Y (s+1+1,t+1+1) ∧
          ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1+1) w
            (eqToHom (congrArg (Sphere (C := Spectrum))
              (show (t+1+1)-(s+1+1)=t-s by omega)) ≫ a ≫ T.f) := by
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨c,hc,hreal,hzero⟩ := prescribed_positive_source_zero_image hcomp T hf s t x a hx ha hfx
  have hm : t-s=(t+1+1)-(s+1+1) := by omega
  let c' : BiHom ((t+1+1)-(s+1+1)) ((t+1+1)-1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) :=
    homotopyRegrade hm (by omega) c
  have hz : (c' ≫ normalizedFirstMap T hf) ≫ XModLambdaN.incl _ 1 = 0 := by
    dsimp only [c']
    rw [←regrade_comp,←regrade_comp,hzero]
    exact regrade_zero _ _
  obtain ⟨b,hb,w,hw,hp,hclass⟩ := full_image_first_label_detects R hcomp _ T.Y
    (normalizedFirstMap T hf) (s+1+1) (t+1+1) c' hz
  refine ⟨c,hc,b,?_,w,hw,hp,?_⟩
  · simpa only [c',regrade_comp] using hb
  · have himage : (R.sphere ((t+1+1)-(s+1+1)) ((t+1+1)-1)).hom ≫
        background.recovery.realization.map (c' ≫ normalizedFirstMap T hf) ≫
          (hcomp.nu T.Y).target.hom =
        eqToHom (congrArg (Sphere (C := Spectrum)) hm.symm) ≫ a ≫ T.f := by
      have hreal' : (R.sphere (t-s) (t+1)).hom ≫ background.recovery.realization.map
          (c ≫ normalizedFirstMap T hf) ≫ (hcomp.nu T.Y).target.hom = a ≫ T.f := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
        rw [normalized_positive_realization_square R hcomp T hf]
        simpa only [Category.assoc] using congrArg (fun z => z ≫ T.f) hreal
      have htransport := realization_homotopy_regrade_full R
        hm (show t+1=(t+1+1)-1 by omega) (c ≫ normalizedFirstMap T hf)
      have ht := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) htransport
      simp only [Category.assoc] at ht
      rw [hreal'] at ht
      simpa only [c',regrade_comp] using ht
    exact himage ▸ hclass

end
end KIP126.ProofTools.Internal.SyntheticCoverage
