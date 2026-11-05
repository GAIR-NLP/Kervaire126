module

public import KIP126.ProofTools.Language

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.Permanence
import all KIP126.ProofTools.SyntheticCoverage.StrictSource
import all KIP126.ProofTools.SyntheticCoverage.CommonLift
import all KIP126.ProofTools.SyntheticCoverage.RawImageComparison
import KIP126.ProofTools.E2Boundary
import KIP126.Literature.Standard.GeneralFiniteQuotient

/-! Actual two-layer error and permanence for the positive first arrow.
The source error ranges over its entire E2 group. All lambda maps, first
labels and classical operations are the fixed normalized ones. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2500000

/-- Coefficient exactness gives the complete Q1 source of every Q2 class
whose first projection is zero, on the actual chosen quotient object. -/
private theorem two_layer_kernel_is_top_first
    (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom m (w-1) (XModLambdaN A 2))
    (ha : a ≫ (background.quotients.tower A).rho 1 2 (by decide) = 0) :
    ∃ e : BiHom m w (XModLambdaN A 1),
      a = finiteTopOfFirst A 1 (by decide) m w e := by
  let T := (background.quotients.tower A).triangle (show 0<1 by decide) (show 1<2 by decide)
  have hz : a ≫ T.rho = 0 := by
    simpa only [T,(background.quotients.tower A).triangle_rho] using ha
  obtain ⟨e,he⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished a hz
  change BiHom m (w-1) ((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN A 1)) at e
  let e' : BiHom m (w+(-1)) ((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN A 1)) :=
    homotopyRegrade rfl (by omega) e
  let z := (verticalTranslate (XModLambdaN A 1) (-1) m w).symm e'
  have hz' : verticalTranslate (XModLambdaN A 1) (-1) m w z = e' :=
    AddEquiv.apply_symm_apply _ _
  refine ⟨z,?_⟩
  change a = e ≫ T.lambdaMap at he
  rw [he]
  unfold finiteTopOfFirst finiteTopInclusion oneInclusionCast
  simp only [Nat.reduceAdd]
  have hshift : homotopyRegrade (m':=m) (w':=w-1) (by simp) (by simp [sub_eq_add_neg])
      (shiftHomotopyClass (0,-((1:ℕ):ℤ)) (m,w) z) = e := by
    have h := congrArg (homotopyRegrade rfl (show w+(-1)=w-1 by omega)) hz'
    simpa [verticalTranslate,regradeAddEquiv,
      suspInvarianceAddEquiv,susp_invariance,Iso.homCongr,shiftHomotopyClass,
      normalized_homotopy_regrade_trans,e',homotopyRegrade] using h
  rw [hshift]

/-- The positive first-arrow error is the actual d2-boundary ambiguity,
with no permanence restriction on the entire E2 source error. -/
private theorem positive_two_layer_error_is_boundary
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ)
    (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))))
    (c : BiHom (t-s) t (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2))
    (b : BiHom ((t+1)-(s+1)) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (w v : Ambient background T.Y (s+1,t+1))
    (hsame : a ≫ XModLambdaN.incl _ 1 = c ≫ (background.quotients.tower _).rho 1 2 (by decide))
    (hc : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) (show t=(t+1)-1 by omega)
      (c ≫ XModLambdaN.map (normalizedFirstMap T hf) 2) =
        finiteTopLabel T.Y 1 (by decide) (s+1) (t+1) v)
    (hb : lambdaMultiply 1 b = homotopyRegrade (by omega) (by omega)
      (a ≫ normalizedFirstMap T hf))
    (hw : b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.Y (s+1) (t+1) w) :
    ∃ e : Ambient background T.X (s,t),
      w-v-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e ∈
        boundaries background T.Y 2 (s+1,t+1) := by
  let A := (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (T.X.obj background.auxiliary))
  let F := normalizedFirstMap T hf
  let d := a ≫ XModLambdaN.incl A 2-c
  have hz : d ≫ (background.quotients.tower A).rho 1 2 (by decide) = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower A).rho_quotient,
      hsame,sub_self]
  let d' : BiHom (t-s) ((t+1)-1) (XModLambdaN A 2) := homotopyRegrade rfl (by omega) d
  have hz' : d' ≫ (background.quotients.tower A).rho 1 2 (by decide) = 0 := by
    dsimp only [d']
    rw [←regrade_comp,hz]
    exact regrade_zero _ _
  obtain ⟨z,hzlabel⟩ := two_layer_kernel_is_top_first A (t-s) (t+1) d' hz'
  let e := (background.firstQuotient T.X 1 s t) z
  have hfirst := normalizedFirstMap_boundary T hf s t e
  dsimp only [e] at hfirst
  rw [LinearEquiv.symm_apply_apply] at hfirst
  have himage : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (d' ≫ XModLambdaN.map F 2) =
      finiteTopLabel T.Y 1 (by decide) (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
    rw [hzlabel,finiteTopOfFirst_natural]
    rw [finiteTopOfFirst_regrade _ 1 (by decide) (t-s) ((t+1)-(s+1))
      (t+1) (t+1) (by omega) rfl]
    exact congrArg (finiteTopOfFirst _ 1 (by decide) ((t+1)-(s+1)) (t+1)) hfirst
  have ht := lambda_first_label_projection_eq_top T.Y (s+1) (t+1) b w hw
  rw [hb,←regrade_comp] at ht
  have hi : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) (show t=(t+1)-1 by omega)
      (d ≫ XModLambdaN.map F 2) =
      finiteTopLabel T.Y 1 (by decide) (s+1) (t+1) w-
        finiteTopLabel T.Y 1 (by decide) (s+1) (t+1) v := by
    dsimp only [d,F]
    rw [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality,←Category.assoc,
      homotopy_regrade_sub,ht,hc]
  have heq : finiteTopLabel T.Y 1 (by decide) (s+1) (t+1) w-
      finiteTopLabel T.Y 1 (by decide) (s+1) (t+1) v =
      finiteTopLabel T.Y 1 (by decide) (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
    rw [←hi]
    simpa only [d',regrade_comp,normalized_homotopy_regrade_trans] using himage
  exact ⟨e,(finite_top_difference_zero_iff_boundary T.Y 1 (by decide) (s+1) (t+1) w v _).mp
    (sub_eq_zero.mpr heq)⟩

public def positiveFirstOperationLinear
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1) (s t : ℤ) :
    Ambient background T.X (s,t) →ₗ[ℤ] Ambient background T.Y (s+1,t+1) where
  toFun := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundaryHom T hf s t
  map_add' := (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundaryHom T hf s t).map_add
  map_smul' := by
    intro n x
    convert! (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundaryHom T hf s t).map_zsmul n x using 1
    · exact congrArg (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundaryHom T hf s t)
        (int_smul_eq_zsmul ..)
    · exact int_smul_eq_zsmul ..

/-- The positive-arrow two-layer terminal argument from actual matching full
and finite sources. It retains the specified realized image. -/
private theorem positive_two_layer_finite_source_permanence
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ)
    (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))))
    (c : BiHom (t-s) t (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2))
    (v : Ambient background T.Y (s+1,t+1))
    (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : permanentCycles background T.Y (s+1,t+1) ≤ P) (hv : v ∈ P)
    (hterminal : (positiveFirstOperationLinear T hf s t).range ⊓ P ≤
      finalBoundaries T.Y (s+1,t+1))
    (hsame : a ≫ XModLambdaN.incl _ 1 = c ≫ (background.quotients.tower _).rho 1 2 (by decide))
    (hc : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) (show t=(t+1)-1 by omega)
      (c ≫ XModLambdaN.map (normalizedFirstMap T hf) 2) =
        finiteTopLabel T.Y 1 (by decide) (s+1) (t+1) v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1,t+1) v
        ((R.sphere ((t+1)-(s+1)) ((t+1)-1)).hom ≫
          background.recovery.realization.map (homotopyRegrade (by omega) (by omega)
            (a ≫ normalizedFirstMap T hf)) ≫ (hcomp.nu T.Y).target.hom) := by
  let F := normalizedFirstMap T hf
  have hczero : (c ≫ XModLambdaN.map F 2) ≫ (background.quotients.tower _).rho 1 2 (by decide) = 0 := by
    have h := congrArg (fun z => z ≫ (background.quotients.tower _).rho 1 2 (by decide)) hc
    rw [two_layer_top_first_zero] at h
    rw [←regrade_comp] at h
    exact (homotopy_regrade_eq_zero _ _ _).mp h
  have hz : (a ≫ F) ≫ XModLambdaN.incl _ 1 = 0 := by
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hsame,
      Category.assoc,(background.quotients.natural F).rho_naturality,←Category.assoc]
    exact hczero
  let a' : BiHom ((t+1)-(s+1)) ((t+1)-1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) := homotopyRegrade (by omega) (by omega) a
  have hz' : (a' ≫ F) ≫ XModLambdaN.incl _ 1 = 0 := by
    dsimp only [a']
    rw [←regrade_comp,←regrade_comp,hz]
    exact regrade_zero _ _
  obtain ⟨b,hb,w,hw,hwp,hdet⟩ := full_image_first_label_detects R hcomp _ T.Y F (s+1) (t+1) a' hz'
  have hb' : lambdaMultiply 1 b = homotopyRegrade (show t-s=(t+1)-(s+1) by omega)
      (show t=(t+1)-1 by omega) (a ≫ F) := by
    simpa only [a',regrade_comp] using hb
  obtain ⟨e,herr⟩ := positive_two_layer_error_is_boundary T hf s t a c b w v hsame hc hb' hw
  have h := classical_detects_of_terminal_image T.X T.Y (s,t) (s+1,t+1)
    (positiveFirstOperationLinear T hf s t)
    P hP hterminal w v hwp hv e 2 herr _ hdet
  simpa only [a',regrade_comp] using h

/-- The positive first-arrow terminal conclusion retains every specified
strict classical source and assumes a common finite two-layer representative. -/
private theorem positive_two_layer_permanence_of_common_lift
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t))
    (a : HomotopyGroup (t-s) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s,t) x a)
    (hfx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0)
    (v : Ambient background T.Y (s+1+1,t+1+1))
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1+1) ≤ P) (hv : v ∈ P)
    (hterminal : (positiveFirstOperationLinear T hf (s+1) (t+1)).range ⊓ P ≤
      finalBoundaries T.Y (s+1+1,t+1+1))
    (c : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 2 (by decide) =
      (background.firstQuotient T.X 1 s t).symm x)
    (himage : c ≫ XModLambdaN.map (normalizedFirstMap T hf) 2 =
      homotopyRegrade (show (t+1+1)-(s+1+1)=t-s by omega) (show (t+1+1)-1=t+1 by omega)
        (finiteTopLabel T.Y 1 (by decide) (s+1+1) (t+1+1) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1+1) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+1+1)-(s+1+1)=t-s by omega)) ≫ a ≫ T.f) := by
  obtain ⟨b,hb,u,hu,w,hw,hwp,hdet⟩ :=
    prescribed_positive_image_first_label_successive hcomp T hf s t x a hx ha hfx
  let b' : BiHom ((t+1)-(s+1)) (t+1) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) := homotopyRegrade (by omega) rfl b
  let c' : BiHom ((t+1)-(s+1)) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2) := homotopyRegrade (by omega) rfl c
  have hsame : b' ≫ XModLambdaN.incl _ 1 =
      c' ≫ (background.quotients.tower _).rho 1 2 (by decide) := by
    dsimp only [b',c']
    rw [←regrade_comp,←regrade_comp,hb,hfirst]
  have hc : homotopyRegrade (show (t+1)-(s+1)=(t+1+1)-(s+1+1) by omega)
      (show t+1=(t+1+1)-1 by omega) (c' ≫ XModLambdaN.map (normalizedFirstMap T hf) 2) =
      finiteTopLabel T.Y 1 (by decide) (s+1+1) (t+1+1) v := by
    dsimp only [c']
    rw [←regrade_comp,himage,normalized_homotopy_regrade_trans,
      normalized_homotopy_regrade_trans]
    rfl
  have hu' : lambdaMultiply 1 u = homotopyRegrade
      (show (t+1)-(s+1)=(t+1+1)-(s+1+1) by omega) (show t+1=(t+1+1)-1 by omega)
        (b' ≫ normalizedFirstMap T hf) := by
    simpa only [b',←regrade_comp,normalized_homotopy_regrade_trans] using hu
  obtain ⟨e,herr⟩ := positive_two_layer_error_is_boundary T hf (s+1) (t+1)
    b' c' u w v hsame hc hu' hw
  exact classical_detects_of_terminal_image T.X T.Y (s+1,t+1) (s+1+1,t+1+1)
    (positiveFirstOperationLinear T hf (s+1) (t+1))
    P hP hterminal w v hwp hv e 2 herr _ hdet

private theorem positive_regrade_self {A : SyntheticSpectrum} {m w : ℤ}
    (hm : m=m) (hw : w=w) (a : BiHom m w A) : homotopyRegrade hm hw a = a := rfl

/-- Positive shifting preserves the exact first restriction of a finite
source; the quotient comparisons are the selected actual ones. -/
private theorem positive_finite_source_first_label
    (X : (AdamsObject (coefficients := background.coefficients))) (s t : ℤ) (x : Ambient background X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (ha : a ≫ (background.quotients.tower _).rho 1 2 (by decide) = nativeFirstLabel X s t x) :
    (verticalTranslate _ 1 (t-s) t a ≫ (levelQuotientShiftIso X 1 2).inv) ≫
      (background.quotients.tower _).rho 1 2 (by decide) =
      (background.firstQuotient X 1 s t).symm x := by
  let e₁ := levelQuotientShiftIso X 1 1
  let e₂ := levelQuotientShiftIso X 1 2
  apply (cancel_mono e₁.hom).mp
  have h := quotient_shift_restriction_on_spheres X (0,1) 1 2 (by decide) (by decide)
    e₁ e₂ (level_quotient_shift_incl X 1 1) (level_quotient_shift_incl X 1 2)
    (t-s) (t+1) (verticalTranslate _ 1 (t-s) t a ≫ e₂.inv)
  simp only [Category.assoc,Iso.inv_hom_id_assoc] at h
  simp only [Category.assoc]
  rw [h,vertical_translate_comp,ha]
  have hl := congrArg (fun z => z ≫ e₁.hom) (positive_first_label_shift X s t x)
  simpa only [e₁,Category.assoc,Iso.inv_hom_id,Category.comp_id] using hl

private theorem ordinary_suspended_injective (A : SyntheticSpectrum) (m w : ℤ) :
    Function.Injective (ordinarySuspendedRepresentative A m w) := by
  intro a b h
  rw [ordinary_suspended_eq_source_iso,ordinary_suspended_eq_source_iso] at h
  have h' := (cancel_epi (ordinarySphereIso m w).hom).mp h
  exact (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor SyntheticSpectrum (1:ℤ))).map_injective h'

/-- A prescribed highest-layer raw image determines the exact native
positive image. Sphere automorphisms act trivially on that specified label. -/
private theorem positive_image_of_raw_top
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (F : (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶ background.nu.functor.obj (Y.obj background.auxiliary))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) 2 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (hε : XModLambdaN.incl _ 2 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 2))
    (ey : XModLambdaN ((background.nu.functor.obj (Y.obj background.auxiliary))⟦(1:ℤ)⟧) 2 ≅
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) 2)⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ 2 ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ 2))
    (s t : ℤ)
    (a : BiHom ((t-s)+1) (t+1) (XModLambdaN
      (((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) 2))
    (a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 2))
    (v : Ambient background Y (s+1+1,(t+1)+1))
    (ha : shiftHomotopyClass (1,1) (t-s,t) a₀ =
      a ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app _) 2 ≫ ε.hom)
    (hi : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map F) 2 ≫ ey.hom =
      ordinarySuspendedRepresentative _ ((t-s)+1) (t+1)
        (homotopyRegrade (show ((t+1)-s)-1=((t-s)+1)-1 by omega)
          (show (t+1)-(0:ℕ)=t+1 by simp) (finiteMayTopLabel Y 0 1 (by decide) s (t+1) v))) :
    homotopyRegrade (show t-s=((t+1)-s)-1 by omega) (show t+1=(t+1)-(0:ℕ) by simp)
      ((verticalTranslate _ 1 (t-s) t a₀ ≫ (levelQuotientShiftIso X 1 2).inv) ≫
        XModLambdaN.map F 2) = finiteMayTopLabel Y 0 1 (by decide) s (t+1) v := by
  obtain ⟨u,hu⟩ := positive_suspended_image_up_to_sphere X Y 2 (by decide) F
    ε (levelQuotientShiftIso X 1 2) hε (level_quotient_shift_incl X 1 2)
    ey hey (t-s) t a a₀ ha
  rw [hi] at hu
  have hh := congrArg (fun z => u.inv ≫ z) hu
  simp only [Iso.inv_hom_id_assoc] at hh
  have hf := ordinary_suspension_sphere_fixed _ ((t-s)+1) (t+1)
    (homotopyRegrade (show ((t+1)-s)-1=((t-s)+1)-1 by omega)
      (show (t+1)-(0:ℕ)=t+1 by simp) (finiteMayTopLabel Y 0 1 (by decide) s (t+1) v))
    (sphere_fixed_regrade (show ((t+1)-s)-1=((t-s)+1)-1 by omega)
      (show (t+1)-(0:ℕ)=t+1 by simp) _
      (finite_may_top_label_sphere_automorphism Y 0 1 (by decide) s (t+1) v)) u.symm
  simp only [Iso.symm_hom] at hf
  rw [hf] at hh
  have heq := (ordinary_suspended_injective _ ((t-s)+1) (t+1)) hh
  have hh' := congrArg (homotopyRegrade
    (show ((t-s)+1)-1=((t+1)-s)-1 by omega)
    (show t+1=(t+1)-(0:ℕ) by simp)) heq
  simpa [verticalTranslate,regradeAddEquiv,suspInvarianceAddEquiv,susp_invariance,
    Iso.homCongr,shiftHomotopyClass,←regrade_comp,normalized_homotopy_regrade_trans,
    positive_regrade_self] using hh'.symm

private theorem ordinary_susp_regrade (A : SyntheticSpectrum) (m m' w w' : ℤ)
    (hm : m=m') (hw : w=w') (a : BiHom (m-1) w A) :
    homotopyRegrade hm hw (ordinarySuspendedRepresentative A m w a) =
      ordinarySuspendedRepresentative A m' w'
        (homotopyRegrade (congrArg (fun z : ℤ => z-1) hm) hw a) := by
  subst m'; subst w'; rfl

/-- The original d2 fold in the positive-first-arrow branch supplies one
actual Q2 source with both the prescribed first label and the exact top image. -/
private theorem two_layer_common_lift_positive_f
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (s t : ℤ) (z : Ambient background T.Z (s,t+1)) (x : Ambient background T.X (s,t))
    (v : Ambient background T.Y (s+1+1,(t+1)+1))
    (hx : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      2 (s,t+1) (s+1+1,(t+1)+1) z
        ((background.classical.map T.g).pageMap 2 (s+1+1,(t+1)+1) v)) :
    ∃ c : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) 2),
      c ≫ (background.quotients.tower _).rho 1 2 (by decide) =
        (background.firstQuotient T.X 1 s t).symm x ∧
      c ≫ XModLambdaN.map (normalizedFirstMap T hf) 2 =
        homotopyRegrade (show ((t+1)+1)-(s+1+1)=t-s by omega)
          (show ((t+1)+1)-1=t+1 by omega)
          (finiteTopLabel T.Y 1 (by decide) (s+1+1) ((t+1)+1) v) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he 2 (by decide)
  obtain ⟨a,c,ha,_,hc,hi⟩ := classical_second_differential_may
    T he hT hg 1 (by decide) s (t+1) z v hd ey hey
  have hfirst := finite_may_source_first_label T he hf hg hh 1 2 (by decide) (by decide)
    s (t+1) z a c ha hc
  obtain ⟨ε,hε,a₀,ha₀,_,hshift⟩ := suspension_finite_target_unshifted T.X 2 (by decide)
    s t x ((background.classical.map T.h).pageMap 2 (s,t+1) z) hx
    (c ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom 2) hfirst
  let c' := homotopyRegrade (show (t+1)-s=(t-s)+1 by omega) rfl c
  let a' := c' ≫ XModLambdaN.map
    ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom) 2
  have hsource : shiftHomotopyClass (1,1) (t-s,t) a₀ =
      a' ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app _) 2 ≫ ε.hom := by
    have hs := congrArg (fun z => z ≫ ε.hom) hshift
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at hs
    have hs' := congrArg (homotopyRegrade (show (t+1)-s=(t-s)+1 by omega) rfl) hs
    dsimp only [a',c']
    rw [Category.assoc,←Category.assoc (XModLambdaN.map _ 2),
      ←background.quotients.functoriality.map_comp,normalizedPositiveSourceIso_suspension T he hf,
      background.quotients.functoriality.map_comp]
    simpa only [←regrade_comp,normalized_homotopy_regrade_trans,Category.assoc,
      positive_regrade_self] using hs'
  have hraw : c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) 2 ≫ ey.hom =
      ordinarySuspendedRepresentative _ ((t+1)-s) (t+1)
        (homotopyRegrade rfl (show (t+1)-(0:ℕ)=t+1 by simp)
          (finiteMayTopLabel T.Y 0 1 (by decide) s (t+1) v)) := by
    have htop := finite_may_signed_target_eq_top_at_level T.Y 0 1 (by decide)
      s (t+1) v ey ey hey hey
    have htop' := congrArg (homotopyRegrade (rfl : (t+1)-s=(t+1)-s)
      (show (t+1)-(0:ℕ)=t+1 by simp)) htop
    rw [regrade_comp,coefficient_insert_zero_regrade,ordinary_susp_regrade_weight] at htop'
    exact hi.trans (by
      simpa only [normalizedTriangle,Triangle.mk,Category.assoc,Iso.inv_hom_id,
        Category.comp_id,Preadditive.neg_comp] using htop')
  have himage : a' ≫ XModLambdaN.map
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedFirstMap T hf)) 2 ≫ ey.hom =
      ordinarySuspendedRepresentative _ ((t-s)+1) (t+1)
        (homotopyRegrade (show ((t+1)-s)-1=((t-s)+1)-1 by omega)
          (show (t+1)-(0:ℕ)=t+1 by simp) (finiteMayTopLabel T.Y 0 1 (by decide) s (t+1) v)) := by
    have hr := congrArg (homotopyRegrade (show (t+1)-s=(t-s)+1 by omega) rfl) hraw
    rw [ordinary_susp_regrade] at hr
    have hmap : (normalizedPositiveSourceIso T hf).hom ≫ normalizedFirstMap T hf =
        (background.normalizedMap T.X T.Y T.f).map := normalizedPositiveSourceIso_map T hf
    dsimp only [a']
    rw [Category.assoc,←Category.assoc (XModLambdaN.map _ 2),
      ←background.quotients.functoriality.map_comp,←Functor.map_comp,hmap]
    simpa only [c',←regrade_comp,normalized_homotopy_regrade_trans,
      normalizedTriangle,Triangle.mk_mor₁] using hr
  have hn := positive_image_of_raw_top T.X T.Y (normalizedFirstMap T hf)
    ε hε ey hey s t a' a₀ v hsource himage
  refine ⟨verticalTranslate _ 1 (t-s) t a₀ ≫ (levelQuotientShiftIso T.X 1 2).inv,
    positive_finite_source_first_label T.X s t x a₀ ha₀,?_⟩
  have hn' := congrArg (homotopyRegrade (show ((t+1)-s)-1=t-s by omega)
    (show (t+1)-(0:ℕ)=t+1 by simp)) hn
  simpa [finiteMayTopLabel,finiteTopLabelAtWeight,
    normalized_homotopy_regrade_trans,positive_regrade_self] using hn'

/-- The actual positive F2 followed by the ordinary G2 is zero for the
same compatible normalized triangle. -/
private theorem positive_first_triangle_composite_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (s t : ℤ) (x : Ambient background T.X (s,t)) :
    (background.classical.map T.g).pageMap 2 (s+1,t+1)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) = 0 := by
  let F := normalizedFirstMap T hf
  have hmap : (normalizedPositiveSourceIso T hf).hom ≫ F =
      (normalizedTriangle background T he).mor₁ := normalizedPositiveSourceIso_map T hf
  have hzero : F ≫ background.nu.functor.map T.g = 0 := by
    apply (cancel_epi (normalizedPositiveSourceIso T hf).hom).mp
    rw [←Category.assoc,hmap,←normalized_second_arrow_zero T he hg,←Category.assoc,
      CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT,zero_comp,comp_zero]
  apply KIP126.ProofTools.Internal.MahowaldLeibniz.native_first_label_injective T.Z (s+1) (t+1)
  rw [←native_first_label_natural,cofiberFirstQuotientBoundary_native_label,
    ←regrade_comp,Category.assoc,quotient_map_comp_zero F (background.nu.functor.map T.g) hzero 1,
    comp_zero,regrade_zero]
  rw [nativeFirstLabel_eq_regrade,map_zero,last_layer_regrade_zero,zero_comp]

private theorem positive_first_terminal_image_of_triangle_kernel
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (s t : ℤ) (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hker : ∀ z : Ambient background T.Y (s+1,t+1), z ∈ P →
      (background.classical.map T.g).pageMap 2 (s+1,t+1) z = 0 →
      IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+1,t+1) z) :
    (positiveFirstOperationLinear T hf s t).range ⊓ P ≤ finalBoundaries T.Y (s+1,t+1) := by
  rintro z ⟨⟨e,rfl⟩,heP⟩
  exact hker _ heP (positive_first_triangle_composite_zero T he hT hf hg s t e)

/-- Two-layer permanence for (alpha,beta,gamma)=(1,0,0).
The finite representative is produced from the original classical d2 fold.
Every specified strict classical source has the same prescribed image. -/
public theorem two_layer_permanence_positive_f
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (s t : ℤ) (_hs : 0 ≤ s)
    (z : Ambient background T.Z (s,t+1)) (x : Ambient background T.X (s,t))
    (v : Ambient background T.Y (s+1+1,(t+1)+1))
    (hH : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      2 (s,t+1) (s+1+1,(t+1)+1) z
        ((background.classical.map T.g).pageMap 2 (s+1+1,(t+1)+1) v))
    (a : HomotopyGroup (t-s) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s,t) x a)
    (hfx : KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x = 0)
    (P : Submodule ℤ (Ambient background T.Y (s+1+1,t+1+1)))
    (hP : permanentCycles background T.Y (s+1+1,t+1+1) ≤ P) (hv : v ∈ P)
    (hker : ∀ z : Ambient background T.Y (s+1+1,t+1+1), z ∈ P →
      (background.classical.map T.g).pageMap 2 (s+1+1,t+1+1) z = 0 →
      IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1+1) z) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1+1,t+1+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1+1,t+1+1) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+1+1)-(s+1+1)=t-s by omega)) ≫ a ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1 :=
    by simp [hf,hg,hh]
  obtain ⟨c,hfirst,himage⟩ := two_layer_common_lift_positive_f T he hT hf hg hh s t z x v hH hd
  exact positive_two_layer_permanence_of_common_lift hcomp T hf s t x a hx ha hfx v P hP hv
    (positive_first_terminal_image_of_triangle_kernel T he hT hf hg (s+1) (t+1) P hker)
    c hfirst himage

end
end KIP126.ProofTools.Internal.SyntheticCoverage
