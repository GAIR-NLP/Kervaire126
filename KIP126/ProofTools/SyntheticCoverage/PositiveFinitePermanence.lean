module

public import KIP126.ProofTools.SyntheticCoverage.PositivePermanence

public import KIP126.ProofTools.SyntheticCoverage.Permanence

public import KIP126.ProofTools.Language

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.PositivePermanence
import all KIP126.ProofTools.SyntheticCoverage.FinitePermanence
import all KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence
import KIP126.Literature.Standard.GeneralFiniteQuotient

/-! Positive-first-arrow finite ambiguity in arbitrary lambda degree.
Every source, quotient map and realized image is retained in the fixed background.
-/

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
set_option maxHeartbeats 4000000

/-- The actual final restriction kernel of any coefficient quotient is
exactly an inserted first-quotient class. -/
private theorem finite_last_kernel_is_top_first
    (A : SyntheticSpectrum) (d : ℕ) (hd : 0<d) (m w : ℤ)
    (a : BiHom m (w-d) (XModLambdaN A (d+1)))
    (ha : a ≫ (background.quotients.tower A).rho d (d+1) (by omega) = 0) :
    ∃ e : BiHom m w (XModLambdaN A 1),
      a = finiteTopOfFirst A d hd m w e := by
  let T := (background.quotients.tower A).triangle hd (Nat.lt_succ_self d)
  have hz : a ≫ T.rho = 0 := by
    simpa only [T,(background.quotients.tower A).triangle_rho] using ha
  obtain ⟨e,he⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished a hz
  change BiHom m (w-d) ((SyntheticCategory.biShift (0,-(d:ℤ))).obj
    (XModLambdaN A ((d+1)-d))) at e
  let e' : BiHom m (w+(-(d:ℤ))) ((SyntheticCategory.biShift (0,-(d:ℤ))).obj
    (XModLambdaN A ((d+1)-d))) := homotopyRegrade rfl (by omega) e
  let z := (verticalTranslate (XModLambdaN A ((d+1)-d)) (-(d:ℤ)) m w).symm e'
  have hz' : verticalTranslate (XModLambdaN A ((d+1)-d)) (-(d:ℤ)) m w z = e' :=
    AddEquiv.apply_symm_apply _ _
  refine ⟨oneQuotientUncast A ((d+1)-d) (by omega) m w z,?_⟩
  change a = e ≫ T.lambdaMap at he
  rw [he,←raw_eq_finiteTopOfFirst]
  have hshift : homotopyRegrade (m':=m) (w':=w-d) (by simp) (by simp [sub_eq_add_neg])
      (shiftHomotopyClass (0,-(d:ℤ)) (m,w) z) = e := by
    have h := congrArg (homotopyRegrade rfl (show w+(-(d:ℤ))=w-d by omega)) hz'
    simpa [verticalTranslate,regradeAddEquiv,suspInvarianceAddEquiv,susp_invariance,
      Iso.homCongr,shiftHomotopyClass,normalized_homotopy_regrade_trans,e',positive_regrade_self] using h
  rw [hshift]

private theorem quotient_unshift_zero_iff
    (X : (AdamsObject (coefficients := background.coefficients))) (δ p : ℤ×ℤ) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
    quotientUnshift X δ p q ε a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hr := shift_quotient_unshift X δ p q ε a
    rw [h] at hr
    simpa [shiftHomotopyClass] using hr.symm
  · intro h
    subst a
    simp only [quotientUnshift,zero_comp,comp_zero]
    apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
    simp

/-- Whole intermediate E3 vanishing moves every error in the shifted
source to its actual last coefficient layer. -/
private theorem positive_finite_first_kernel_is_top_first_of_third_page_vanishes
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0<d) (s t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (X.obj background.auxiliary)).Page 3 (s-d+j,t-d+j)))
    (a : BiHom (t-s) (t+1-d) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) (d+1)))
    (ha : a ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) = 0) :
    ∃ e : Ambient background X (s,t),
      a = finiteTopOfFirst _ d hd (t-s) (t+1) ((background.firstQuotient X 1 s t).symm e) := by
  let a' : BiHom ((t-s,t-d)+(0,1)).1 ((t-s,t-d)+(0,1)).2
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) (d+1)) := homotopyRegrade (by simp) (by dsimp; omega) a
  let a₀ := quotientUnshift X (0,1) (t-s,t-d) (d+1) (levelQuotientShiftIso X 1 (d+1)) a'
  have hz' : a' ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) = 0 := by
    dsimp only [a']
    rw [←regrade_comp,ha,regrade_zero]
  have hz₀ : a₀ ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) = 0 := by
    dsimp only [a₀]
    rw [quotient_unshift_restriction X (0,1) (t-s,t-d) 1 (d+1) (by decide) (by omega)
      (levelQuotientShiftIso X 1 1) (levelQuotientShiftIso X 1 (d+1))
      (level_quotient_shift_incl X 1 1) (level_quotient_shift_incl X 1 (d+1)),hz']
    exact (quotient_unshift_zero_iff _ _ _ _ _ _).mpr rfl
  obtain ⟨e,he⟩ := finite_first_kernel_is_top_label_of_third_page_vanishes X d hd s t hmid a₀ hz₀
  have hlast₀ : a₀ ≫ (background.quotients.tower _).rho d (d+1) (by omega) = 0 := by
    rw [he,finite_top_restriction_zero]
  have hlast' : a' ≫ (background.quotients.tower _).rho d (d+1) (by omega) = 0 := by
    apply (quotient_unshift_zero_iff X (0,1) (t-s,t-d) d (levelQuotientShiftIso X 1 d) _).mp
    rw [←quotient_unshift_restriction X (0,1) (t-s,t-d) d (d+1) hd (by omega)
      (levelQuotientShiftIso X 1 d) (levelQuotientShiftIso X 1 (d+1))
      (level_quotient_shift_incl X 1 d) (level_quotient_shift_incl X 1 (d+1))]
    exact hlast₀
  have hlast : a ≫ (background.quotients.tower _).rho d (d+1) (by omega) = 0 := by
    dsimp only [a'] at hlast'
    rw [←regrade_comp] at hlast'
    exact (homotopy_regrade_eq_zero _ _ _).mp hlast'
  obtain ⟨z,hz⟩ := finite_last_kernel_is_top_first _ d hd (t-s) (t+1) a hlast
  refine ⟨background.firstQuotient X 1 s t z,?_⟩
  simpa only [LinearEquiv.symm_apply_apply] using hz

/-- Positive F2 measures the complete last-layer source error. -/
private theorem positive_finite_error_is_boundary_of_third_page_vanishes
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (T.X.obj background.auxiliary)).Page 3 (s-d+j,t-d+j)))
    (a : BiHom (t-s) (t+1-d) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))))
    (c : BiHom (t-s) (t+1-d) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1)))
    (b : BiHom ((t+1)-(s+1)) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (w v : Ambient background T.Y (s+1,t+1))
    (hsame : a ≫ XModLambdaN.incl _ 1 = c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (c ≫ XModLambdaN.map (normalizedFirstMap T hf) (d+1)) =
        finiteTopLabel T.Y d hd (s+1) (t+1) v)
    (hb : lambdaMultiply d b = homotopyRegrade (by omega) rfl (a ≫ normalizedFirstMap T hf))
    (hw : b ≫ XModLambdaN.incl _ 1 = nativeFirstLabel T.Y (s+1) (t+1) w) :
    ∃ e : Ambient background T.X (s,t),
      w-v-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e ∈
        boundaries background T.Y (d+1) (s+1,t+1) := by
  let A := (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (T.X.obj background.auxiliary))
  let F := normalizedFirstMap T hf
  let e₀ := a ≫ XModLambdaN.incl A (d+1)-c
  have hz : e₀ ≫ (background.quotients.tower A).rho 1 (d+1) (by omega) = 0 := by
    dsimp only [e₀]
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower A).rho_quotient,hsame,sub_self]
  obtain ⟨e,he⟩ := positive_finite_first_kernel_is_top_first_of_third_page_vanishes
    T.X d hd s t hmid e₀ hz
  have himage : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (e₀ ≫ XModLambdaN.map F (d+1)) =
      finiteTopLabel T.Y d hd (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
    rw [he,finiteTopOfFirst_natural]
    rw [finiteTopOfFirst_regrade _ d hd (t-s) ((t+1)-(s+1)) (t+1) (t+1) (by omega) rfl]
    exact congrArg (finiteTopOfFirst _ d hd ((t+1)-(s+1)) (t+1))
      (normalizedFirstMap_boundary T hf s t e)
  have ht := lambda_power_first_label_projection_eq_top T.Y d hd (s+1) (t+1) b w hw
  rw [hb,←regrade_comp] at ht
  dsimp only [e₀,F] at himage
  rw [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality,←Category.assoc,
    homotopy_regrade_sub,ht,hc] at himage
  exact ⟨e,(finite_top_difference_zero_iff_boundary T.Y d hd (s+1) (t+1) w v _).mp
    (sub_eq_zero.mpr himage)⟩

/-- The general positive finite comparison obtains the needed full
lambda^d preimage internally and retains its realized image. -/
private theorem positive_finite_source_permanence_of_third_page_vanishes
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (T.X.obj background.auxiliary)).Page 3 (s-d+j,t-d+j)))
    (a : BiHom (t-s) (t+1-d) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))))
    (c : BiHom (t-s) (t+1-d) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1)))
    (v : Ambient background T.Y (s+1,t+1)) (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : permanentCycles background T.Y (s+1,t+1) ≤ P) (hv : v ∈ P)
    (hterminal : (positiveFirstOperationLinear T hf s t).range ⊓ P ≤ finalBoundaries T.Y (s+1,t+1))
    (hsame : a ≫ XModLambdaN.incl _ 1 = c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega))
    (hc : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (c ≫ XModLambdaN.map (normalizedFirstMap T hf) (d+1)) =
        finiteTopLabel T.Y d hd (s+1) (t+1) v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1,t+1) v
        ((R.sphere ((t+1)-(s+1)) ((t+1)-d)).hom ≫
          background.recovery.realization.map (homotopyRegrade (by omega) rfl
            (a ≫ normalizedFirstMap T hf)) ≫ (hcomp.nu T.Y).target.hom) := by
  let A := (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (T.X.obj background.auxiliary))
  let F := normalizedFirstMap T hf
  let e₀ := a ≫ XModLambdaN.incl A (d+1)-c
  have hz : e₀ ≫ (background.quotients.tower A).rho 1 (d+1) (by omega) = 0 := by
    dsimp only [e₀]
    rw [Preadditive.sub_comp,Category.assoc,(background.quotients.tower A).rho_quotient,hsame,sub_self]
  obtain ⟨e,he⟩ := positive_finite_first_kernel_is_top_first_of_third_page_vanishes
    T.X d hd s t hmid e₀ hz
  have himage : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (e₀ ≫ XModLambdaN.map F (d+1)) =
      finiteTopLabel T.Y d hd (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
    rw [he,finiteTopOfFirst_natural]
    rw [finiteTopOfFirst_regrade _ d hd (t-s) ((t+1)-(s+1)) (t+1) (t+1) (by omega) rfl]
    exact congrArg (finiteTopOfFirst _ d hd ((t+1)-(s+1)) (t+1))
      (normalizedFirstMap_boundary T hf s t e)
  dsimp only [e₀,F] at himage
  rw [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality,←Category.assoc,
    homotopy_regrade_sub,hc] at himage
  have hzero : (a ≫ F) ≫ XModLambdaN.incl _ d = 0 := by
    have h := congrArg (fun z => z ≫ (background.quotients.tower
      (background.nu.functor.obj (T.Y.obj background.auxiliary))).rho d (d+1) (by omega)) himage
    rw [Preadditive.sub_comp,←regrade_comp,Category.assoc,(background.quotients.tower _).rho_quotient,
      finite_top_restriction_zero,finite_top_restriction_zero,sub_zero] at h
    exact (homotopy_regrade_eq_zero _ _ _).mp h
  let a' : BiHom ((t+1)-(s+1)) ((t+1)-d) A := homotopyRegrade (by omega) rfl a
  have hzero' : (a' ≫ F) ≫ XModLambdaN.incl _ d = 0 := by
    dsimp only [a']
    rw [←regrade_comp,←regrade_comp,hzero,regrade_zero]
  obtain ⟨b,hb,w,hw,hwp,hdet⟩ := full_image_lambda_power_first_label_detects R hcomp A T.Y F d
    (s+1) (t+1) a' hzero'
  have hb' : lambdaMultiply d b = homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (a ≫ F) := by simpa only [a',regrade_comp] using hb
  obtain ⟨e,herr⟩ := positive_finite_error_is_boundary_of_third_page_vanishes T hf d hd s t
    hmid a c b w v hsame hc hb' hw
  have h := classical_detects_of_terminal_image T.X T.Y (s,t) (s+1,t+1)
    (positiveFirstOperationLinear T hf s t) P hP hterminal w v hwp hv e (d+1) herr _ hdet
  simpa only [a',regrade_comp] using h

/-- The specified strict classical source is lifted internally, with its
realization fixed exactly, before the general positive finite comparison. -/
private theorem positive_finite_permanence_of_common_lift
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (T.X.obj background.auxiliary)).Page 3 (s+j,t+j)))
    (x : Ambient background T.X (s,t)) (a : HomotopyGroup (t-s) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s,t) x a)
    (v : Ambient background T.Y (s+d+1,t+d+1))
    (P : Submodule ℤ (Ambient background T.Y (s+d+1,t+d+1)))
    (hP : permanentCycles background T.Y (s+d+1,t+d+1) ≤ P) (hv : v ∈ P)
    (hterminal : (positiveFirstOperationLinear T hf (s+d) (t+d)).range ⊓ P ≤
      finalBoundaries T.Y (s+d+1,t+d+1))
    (c : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1)))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) =
      (background.firstQuotient T.X 1 s t).symm x)
    (himage : c ≫ XModLambdaN.map (normalizedFirstMap T hf) (d+1) =
      homotopyRegrade (show (t+d+1)-(s+d+1)=t-s by omega)
        (show (t+d+1)-d=t+1 by omega) (finiteTopLabel T.Y d hd (s+d+1) (t+d+1) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,t+d+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,t+d+1) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ a ≫ T.f) := by
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨b,hb,hreal⟩ := prescribed_native_source hcomp T.X s t x a hx ha
  let b₁ := verticalTranslate _ 1 (t-s) t b
  have hb₁ := positive_full_source_first_label T.X s t x b hb
  have hreal₁ : (R.sphere (t-s) (t+1)).hom ≫ background.recovery.realization.map b₁ ≫
      (hcomp.shiftedNu T.X 1).target.hom = a :=
    (positive_source_realization_eq R hcomp T.X 1 (t-s) t b).trans hreal
  let b' : BiHom ((t+d)-(s+d)) (t+d+1-d) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) := homotopyRegrade (by omega) (by omega) b₁
  let c' : BiHom ((t+d)-(s+d)) (t+d+1-d) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1)) := homotopyRegrade (by omega) (by omega) c
  have hsame : b' ≫ XModLambdaN.incl _ 1 = c' ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) := by
    dsimp only [b',c']
    rw [←regrade_comp,←regrade_comp,hb₁,hfirst]
  have hc : homotopyRegrade (show (t+d)-(s+d)=(t+d+1)-(s+d+1) by omega) rfl
      (c' ≫ XModLambdaN.map (normalizedFirstMap T hf) (d+1)) =
      finiteTopLabel T.Y d hd (s+d+1) (t+d+1) v := by
    dsimp only [c']
    rw [←regrade_comp,himage,normalized_homotopy_regrade_trans,normalized_homotopy_regrade_trans]
    rfl
  obtain ⟨hp,hdet⟩ := positive_finite_source_permanence_of_third_page_vanishes R hcomp T hf d hd
    (s+d) (t+d) (by intro j hj hjd; simpa only [add_sub_cancel_right] using hmid j hj hjd)
    b' c' v P hP hv hterminal hsame hc
  refine ⟨hp,?_⟩
  have hreal' : (R.sphere (t-s) (t+1)).hom ≫ background.recovery.realization.map
      (b₁ ≫ normalizedFirstMap T hf) ≫ (hcomp.nu T.Y).target.hom = a ≫ T.f := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [normalized_positive_realization_square R hcomp T hf]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ T.f) hreal₁
  have htransport := realization_homotopy_regrade_full R
    (show t-s=(t+d+1)-(s+d+1) by omega) (show t+1=(t+d+1)-d by omega)
    (b₁ ≫ normalizedFirstMap T hf)
  have ht := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) htransport
  simp only [Category.assoc] at ht
  rw [hreal'] at ht
  have hreal'' : (R.sphere ((t+d+1)-(s+d+1)) ((t+d+1)-d)).hom ≫
      background.recovery.realization.map (homotopyRegrade (by omega) rfl (b' ≫ normalizedFirstMap T hf)) ≫
      (hcomp.nu T.Y).target.hom =
      eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ a ≫ T.f := by
    simpa only [b',←regrade_comp,normalized_homotopy_regrade_trans] using ht
  exact hreal'' ▸ hdet

private theorem positive_finite_source_first_label_general
    (X : (AdamsObject (coefficients := background.coefficients))) (N : ℕ) (hN : 0<N) (s t : ℤ) (x : Ambient background X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (ha : a ≫ (background.quotients.tower _).rho 1 N hN = nativeFirstLabel X s t x) :
    (verticalTranslate _ 1 (t-s) t a ≫ (levelQuotientShiftIso X 1 N).inv) ≫
      (background.quotients.tower _).rho 1 N hN = (background.firstQuotient X 1 s t).symm x := by
  let e₁ := levelQuotientShiftIso X 1 1
  let eN := levelQuotientShiftIso X 1 N
  apply (cancel_mono e₁.hom).mp
  have h := quotient_shift_restriction_on_spheres X (0,1) 1 N (by decide) hN
    e₁ eN (level_quotient_shift_incl X 1 1) (level_quotient_shift_incl X 1 N)
    (t-s) (t+1) (verticalTranslate _ 1 (t-s) t a ≫ eN.inv)
  simp only [Category.assoc,Iso.inv_hom_id_assoc] at h
  simp only [Category.assoc]
  rw [h,vertical_translate_comp,ha]
  have hl := congrArg (fun z => z ≫ e₁.hom) (positive_first_label_shift X s t x)
  simpa only [e₁,Category.assoc,Iso.inv_hom_id,Category.comp_id] using hl

/-- The exact raw-to-native top comparison for arbitrary coefficient
length. The sphere automorphism is removed only on the specified top label. -/
private theorem positive_finite_image_of_raw_top
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (F : (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶ background.nu.functor.obj (Y.obj background.auxiliary))
    (d : ℕ) (hd : 0<d)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) (d+1) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (hε : XModLambdaN.incl _ (d+1) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (d+1)))
    (ey : XModLambdaN ((background.nu.functor.obj (Y.obj background.auxiliary))⟦(1:ℤ)⟧) (d+1) ≅
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (d+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (d+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (d+1)))
    (s t p u : ℤ) (hm : u-p=t-s) (hw : u-d=t+1)
    (a : BiHom ((t-s)+1) (t+1) (XModLambdaN
      (((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) (d+1)))
    (a₀ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (d+1)))
    (v : Ambient background Y (p,u))
    (ha : shiftHomotopyClass (1,1) (t-s,t) a₀ =
      a ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app _) (d+1) ≫ ε.hom)
    (hi : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map F) (d+1) ≫ ey.hom =
      ordinarySuspendedRepresentative _ ((t-s)+1) (t+1)
        (homotopyRegrade (show u-p=((t-s)+1)-1 by omega) hw (finiteTopLabel Y d hd p u v))) :
    (verticalTranslate _ 1 (t-s) t a₀ ≫ (levelQuotientShiftIso X 1 (d+1)).inv) ≫
      XModLambdaN.map F (d+1) = homotopyRegrade hm hw (finiteTopLabel Y d hd p u v) := by
  obtain ⟨k,hk⟩ := positive_suspended_image_up_to_sphere X Y (d+1) (by omega) F
    ε (levelQuotientShiftIso X 1 (d+1)) hε (level_quotient_shift_incl X 1 (d+1))
    ey hey (t-s) t a a₀ ha
  rw [hi] at hk
  have hh := congrArg (fun z => k.inv ≫ z) hk
  simp only [Iso.inv_hom_id_assoc] at hh
  have hfixed := ordinary_suspension_sphere_fixed _ ((t-s)+1) (t+1)
    (homotopyRegrade (show u-p=((t-s)+1)-1 by omega) hw (finiteTopLabel Y d hd p u v))
    (sphere_fixed_regrade (show u-p=((t-s)+1)-1 by omega) hw _
      (finite_top_label_sphere_automorphism Y d hd p u v)) k.symm
  simp only [Iso.symm_hom] at hfixed
  rw [hfixed] at hh
  have heq := (ordinary_suspended_injective _ ((t-s)+1) (t+1)) hh
  have hh' := congrArg (homotopyRegrade (show ((t-s)+1)-1=t-s by omega) (rfl : t+1=t+1)) heq
  simpa [verticalTranslate,regradeAddEquiv,suspInvarianceAddEquiv,susp_invariance,
    Iso.homCongr,shiftHomotopyClass,←regrade_comp,normalized_homotopy_regrade_trans,
    positive_regrade_self] using hh'.symm

/-- The original higher differential supplies the common positive finite
source, with its exact original first label and its exact prescribed top image. -/
private theorem finite_common_lift_positive_f
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (z : Ambient background T.Z (s,t+1)) (x : Ambient background T.X (s,t))
    (v : Ambient background T.Y (s+d+1,(t+1)+d))
    (hx : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hdiff : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (d+1) (s,t+1) (s+d+1,(t+1)+d) z
        ((background.classical.map T.g).pageMap 2 (s+d+1,(t+1)+d) v)) :
    ∃ c : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1)),
      c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) =
        (background.firstQuotient T.X 1 s t).symm x ∧
      c ≫ XModLambdaN.map (normalizedFirstMap T hf) (d+1) =
        homotopyRegrade (show ((t+1)+d)-(s+d+1)=t-s by omega)
          (show ((t+1)+d)-d=t+1 by omega)
          (finiteTopLabel T.Y d hd (s+d+1) ((t+1)+d) v) := by
  obtain ⟨ey,hey,_⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (d+1) (by omega)
  obtain ⟨a,c,ha,_,hc,hi⟩ := classical_second_differential_may
    T he hT hg d hd s (t+1) z v hdiff ey hey
  have hfirst := finite_may_source_first_label T he hf hg hh d (d+1) hd (by omega)
    s (t+1) z a c ha hc
  obtain ⟨ε,hε,a₀,ha₀,_,hshift⟩ := suspension_finite_target_unshifted T.X (d+1) (by omega)
    s t x ((background.classical.map T.h).pageMap 2 (s,t+1) z) hx
    (c ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (d+1)) hfirst
  let c' := homotopyRegrade (show (t+1)-s=(t-s)+1 by omega) rfl c
  let a' := c' ≫ XModLambdaN.map
    ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedPositiveSourceIso T hf).hom) (d+1)
  have hsource : shiftHomotopyClass (1,1) (t-s,t) a₀ =
      a' ≫ XModLambdaN.map (positiveOrdinaryIso.hom.app _) (d+1) ≫ ε.hom := by
    have hs := congrArg (fun z => z ≫ ε.hom) hshift
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at hs
    have hs' := congrArg (homotopyRegrade (show (t+1)-s=(t-s)+1 by omega) rfl) hs
    dsimp only [a',c']
    rw [Category.assoc,←Category.assoc (XModLambdaN.map _ (d+1)),
      ←background.quotients.functoriality.map_comp,normalizedPositiveSourceIso_suspension T he hf,
      background.quotients.functoriality.map_comp]
    simpa only [←regrade_comp,normalized_homotopy_regrade_trans,Category.assoc,positive_regrade_self] using hs'
  have hraw : c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (d+1) ≫ ey.hom =
      ordinarySuspendedRepresentative _ ((t+1)-s) (t+1)
        (homotopyRegrade (show ((t+1)+d)-(s+d+1)=((t+1)-s)-1 by omega)
          (show ((t+1)+d)-d=t+1 by omega)
          (finiteTopLabel T.Y d hd (s+d+1) ((t+1)+d) v)) := by
    exact hi.trans (by simpa only [normalizedTriangle,Triangle.mk] using
      ordinary_may_signed_top_target T.Y d hd s (t+1) v)
  have himage : a' ≫ XModLambdaN.map
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (normalizedFirstMap T hf)) (d+1) ≫ ey.hom =
      ordinarySuspendedRepresentative _ ((t-s)+1) (t+1)
        (homotopyRegrade (show ((t+1)+d)-(s+d+1)=((t-s)+1)-1 by omega)
          (show ((t+1)+d)-d=t+1 by omega) (finiteTopLabel T.Y d hd (s+d+1) ((t+1)+d) v)) := by
    have hr := congrArg (homotopyRegrade (show (t+1)-s=(t-s)+1 by omega) rfl) hraw
    rw [ordinary_susp_regrade] at hr
    have hmap : (normalizedPositiveSourceIso T hf).hom ≫ normalizedFirstMap T hf =
        (background.normalizedMap T.X T.Y T.f).map := normalizedPositiveSourceIso_map T hf
    dsimp only [a']
    rw [Category.assoc,←Category.assoc (XModLambdaN.map _ (d+1)),
      ←background.quotients.functoriality.map_comp,←Functor.map_comp,hmap]
    simpa only [c',←regrade_comp,normalized_homotopy_regrade_trans,
      normalizedTriangle,Triangle.mk_mor₁] using hr
  refine ⟨verticalTranslate _ 1 (t-s) t a₀ ≫ (levelQuotientShiftIso T.X 1 (d+1)).inv,
    positive_finite_source_first_label_general T.X (d+1) (by omega) s t x a₀ ha₀,?_⟩
  exact positive_finite_image_of_raw_top T.X T.Y (normalizedFirstMap T hf) d hd
    ε hε ey hey s t (s+d+1) ((t+1)+d) (by omega) (by omega) a' a₀ v hsource himage

/-- The same actual positive first operation in an equal target bidegree. -/
public def positiveFirstOperationLinearAt
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (s t p u : ℤ) (hp : p=s+1) (hu : u=t+1) :
    Ambient background T.X (s,t) →ₗ[ℤ] Ambient background T.Y (p,u) := by
  subst p; subst u
  exact positiveFirstOperationLinear T hf s t

/-- Equality-only coordinate transport for the original whole-image
terminal condition. The target retains the classical fold's coordinates. -/
private theorem positive_finite_permanence_of_common_lift_at
    (hcomp : LambdaInversionAdamsComparison background KIP126.Literature.Standard.realizationData)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (d : ℕ) (hd : 0<d) (s t p u : ℤ) (hp : p=s+d+1) (hu : u=t+d+1)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (T.X.obj background.auxiliary)).Page 3 (s+j,t+j)))
    (x : Ambient background T.X (s,t)) (a : HomotopyGroup (t-s) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s,t) x a)
    (v : Ambient background T.Y (p,u)) (P : Submodule ℤ (Ambient background T.Y (p,u)))
    (hP : permanentCycles background T.Y (p,u) ≤ P) (hv : v ∈ P)
    (hterminal : (positiveFirstOperationLinearAt T hf (s+d) (t+d) p u hp hu).range ⊓ P ≤
      finalBoundaries T.Y (p,u))
    (c : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1)))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega) =
      (background.firstQuotient T.X 1 s t).symm x)
    (himage : c ≫ XModLambdaN.map (normalizedFirstMap T hf) (d+1) =
      homotopyRegrade (show u-p=t-s by omega) (show u-d=t+1 by omega)
        (finiteTopLabel T.Y d hd p u v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (p,u) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (p,u) v
        (eqToHom (congrArg (Sphere (C := Spectrum)) (show u-p=t-s by omega)) ≫ a ≫ T.f) := by
  subst p; subst u
  exact positive_finite_permanence_of_common_lift hcomp T hf d hd s t hmid x a hx ha v P hP hv
    hterminal c hfirst himage

/-- Finite permanence in the positive-first-arrow branch.
The original d_(d+1) fold produces the common quotient representative.
The entire intermediate E3 groups and the original whole-image terminal
condition control all ambiguities, and the specified classical source is retained. -/
public theorem finite_permanence_positive_f
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (d : ℕ) (hd : 0<d) (s t : ℤ) (_hs : 0 ≤ s)
    (hmid : ∀ j : ℕ, 1 ≤ j → j ≤ d-1 →
      Subsingleton ((background.classical.obj (T.X.obj background.auxiliary)).Page 3 (s+j,t+j)))
    (z : Ambient background T.Z (s,t+1)) (x : Ambient background T.X (s,t))
    (v : Ambient background T.Y (s+d+1,(t+1)+d))
    (hH : (background.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((background.classical.map T.h).pageMap 2 (s,t+1) z) (by simpa using x))
    (hdiff : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (d+1) (s,t+1) (s+d+1,(t+1)+d) z
        ((background.classical.map T.g).pageMap 2 (s+d+1,(t+1)+d) v))
    (a : HomotopyGroup (t-s) (T.X.obj background.auxiliary))
    (hx : NonzeroSurvival (background.classical.obj (T.X.obj background.auxiliary)) (s,t) x)
    (ha : ClassicalDetects (background.classicalConvergence T.X) (s,t) x a)
    (P : Submodule ℤ (Ambient background T.Y (s+d+1,(t+1)+d)))
    (hP : permanentCycles background T.Y (s+d+1,(t+1)+d) ≤ P) (hv : v ∈ P)
    (hterminal : (positiveFirstOperationLinearAt T hf (s+d) (t+d)
      (s+d+1) ((t+1)+d) rfl (by omega)).range ⊓ P ≤
      finalBoundaries T.Y (s+d+1,(t+1)+d)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,(t+1)+d) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,(t+1)+d) v
        (eqToHom (congrArg (Sphere (C := Spectrum))
          (show ((t+1)+d)-(s+d+1)=t-s by omega)) ≫ a ≫ T.f) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨c,hfirst,himage⟩ := finite_common_lift_positive_f T (by simp [hf,hg,hh])
    hT hf hg hh d hd s t z x v hH hdiff
  exact positive_finite_permanence_of_common_lift_at hcomp T hf d hd s t
    (s+d+1) ((t+1)+d) rfl (by omega) hmid x a hx ha v P hP hv hterminal c hfirst himage

/-- Every shifted finite class in the last filtration is
an inserted first-quotient class. -/
private theorem positive_finite_top_of_filtration
    (X : (AdamsObject (coefficients := background.coefficients))) (d : ℕ) (hd : 0<d) (s t : ℤ)
    (a : BiHom (t-s) (t+1-d) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) (d+1)))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    ∃ e : Ambient background X (s,t),
      a = finiteTopOfFirst _ d hd (t-s) (t+1) ((background.firstQuotient X 1 s t).symm e) := by
  let ρ := (background.quotients.tower ((SyntheticCategory.biShift (0,1)).obj
    (background.nu.functor.obj (X.obj background.auxiliary)))).rho d (d+1) (by omega)
  let E := levelQuotientShiftIso X 1 d
  have hfil := map_preserves_filtration (background.convergentMap
    (.quotient (d+1) (.shift (0,1) (.nu X))) (.shift (0,1) (.quotient d (.nu X)))
    (ρ ≫ E.hom)) (t-s,t+1-d) s a ha
  have hz := shifted_finite_high_filtration_zero X d hd 1 (t-s) (t+1-d) s (by omega)
    (a ≫ ρ ≫ E.hom) hfil
  have hρ : a ≫ ρ = 0 := by
    apply (cancel_mono E.hom).mp
    simpa only [Category.assoc,zero_comp] using hz
  obtain ⟨z,hz⟩ := finite_last_kernel_is_top_first _ d hd (t-s) (t+1) a hρ
  refine ⟨background.firstQuotient X 1 s t z,?_⟩
  simpa only [LinearEquiv.symm_apply_apply] using hz

/-- The affine terminal comparison for the positive first arrow,
with an explicit last-filtration hypothesis. The full torsion correction
disappears under the same realization. -/
private theorem positive_affine_last_filtration_permanence
    (R : RealizationCoordinates background)
    (hcomp : LambdaInversionAdamsComparison background R)
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (a : BiHom (t-s) (t+1-d) ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))))
    (c : BiHom (t-s) (t+1-d) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (d+1)))
    (D : BiHom (t-s) (t+1-d) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (N : ℕ) (hD : lambdaMultiply N D = 0)
    (v : Ambient background T.Y (s+1,t+1)) (P : Submodule ℤ (Ambient background T.Y (s+1,t+1)))
    (hP : permanentCycles background T.Y (s+1,t+1) ≤ P) (hv : v ∈ P)
    (hterminal : (positiveFirstOperationLinear T hf s t).range ⊓ P ≤ finalBoundaries T.Y (s+1,t+1))
    (hfil : FiltrationAtLeast background.syntheticTower s (a ≫ XModLambdaN.incl _ (d+1)-c))
    (hc : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      (c ≫ XModLambdaN.map (normalizedFirstMap T hf) (d+1)) =
        homotopyRegrade (by omega) rfl (D ≫ XModLambdaN.incl _ (d+1)) +
          finiteTopLabel T.Y d hd (s+1) (t+1) v) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+1,t+1) v ∧
      ClassicalDetects (background.classicalConvergence T.Y) (s+1,t+1) v
        ((R.sphere ((t+1)-(s+1)) ((t+1)-d)).hom ≫
          background.recovery.realization.map (homotopyRegrade (by omega) rfl
            (a ≫ normalizedFirstMap T hf)) ≫ (hcomp.nu T.Y).target.hom) := by
  let A := (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj (T.X.obj background.auxiliary))
  let F := normalizedFirstMap T hf
  let B := background.nu.functor.obj (T.Y.obj background.auxiliary)
  letI := R.additive
  obtain ⟨e,he⟩ := positive_finite_top_of_filtration T.X d hd s t
    (a ≫ XModLambdaN.incl A (d+1)-c) hfil
  have himage : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      ((a ≫ XModLambdaN.incl A (d+1)-c) ≫ XModLambdaN.map F (d+1)) =
      finiteTopLabel T.Y d hd (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
    rw [he,finiteTopOfFirst_natural]
    rw [finiteTopOfFirst_regrade _ d hd (t-s) ((t+1)-(s+1)) (t+1) (t+1) (by omega) rfl]
    exact congrArg (finiteTopOfFirst _ d hd ((t+1)-(s+1)) (t+1))
      (normalizedFirstMap_boundary T hf s t e)
  rw [Preadditive.sub_comp,Category.assoc,←XModLambdaN.incl_naturality,←Category.assoc,
    homotopy_regrade_sub,hc] at himage
  have hcorrected : homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
      ((a ≫ F-D) ≫ XModLambdaN.incl B (d+1)) =
      finiteTopLabel T.Y d hd (s+1) (t+1) v +
        finiteTopLabel T.Y d hd (s+1) (t+1)
          (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e) := by
    rw [Preadditive.sub_comp,homotopy_regrade_sub]
    apply sub_eq_iff_eq_add.mpr
    exact (sub_eq_iff_eq_add.mp himage).trans (by abel)
  have hzero : (a ≫ F-D) ≫ XModLambdaN.incl B d = 0 := by
    have h := congrArg (fun z => z ≫ (background.quotients.tower B).rho d (d+1) (by omega)) hcorrected
    rw [←regrade_comp,Category.assoc,(background.quotients.tower B).rho_quotient,
      Preadditive.add_comp,finite_top_restriction_zero,finite_top_restriction_zero,zero_add] at h
    exact (homotopy_regrade_eq_zero _ _ _).mp h
  let z : BiHom ((t+1)-(s+1)) ((t+1)-d) B := homotopyRegrade (by omega) rfl (a ≫ F-D)
  have hzero' : (z ≫ 𝟙 B) ≫ XModLambdaN.incl B d = 0 := by
    rw [Category.comp_id]
    dsimp only [z]
    rw [←regrade_comp,hzero,regrade_zero]
  obtain ⟨b,hb,w,hw,hwp,hdet⟩ := full_image_lambda_power_first_label_detects R hcomp B T.Y
    (𝟙 B) d (s+1) (t+1) z hzero'
  rw [Category.comp_id] at hb hdet
  have ht := lambda_power_first_label_projection_eq_top T.Y d hd (s+1) (t+1) b w hw
  rw [hb] at ht
  dsimp only [z] at ht
  rw [←regrade_comp] at ht
  have hwt := ht.symm.trans hcorrected
  have herr : w-v-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t e ∈
      boundaries background T.Y (d+1) (s+1,t+1) := by
    apply (finite_top_difference_zero_iff_boundary T.Y d hd (s+1) (t+1) w v _).mp
    rw [hwt]
    abel
  have hDzero := lambda_torsion_realization_zero R (t-s) (t+1-d) N D hD
  have hrawreal : (R.sphere (t-s) (t+1-d)).hom ≫ background.recovery.realization.map (a ≫ F-D) ≫
      (hcomp.nu T.Y).target.hom =
      (R.sphere (t-s) (t+1-d)).hom ≫ background.recovery.realization.map (a ≫ F) ≫
        (hcomp.nu T.Y).target.hom := by
    rw [Functor.map_sub,Preadditive.sub_comp,Preadditive.comp_sub]
    have hDzero' := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) hDzero
    simp only [Category.assoc,zero_comp] at hDzero'
    rw [hDzero',sub_zero]
  have htransport₀ := realization_homotopy_regrade_full R
    (show t-s=(t+1)-(s+1) by omega) rfl (a ≫ F-D)
  have htransport₁ := realization_homotopy_regrade_full R
    (show t-s=(t+1)-(s+1) by omega) rfl (a ≫ F)
  have h₀ := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) htransport₀
  have h₁ := congrArg (fun z => z ≫ (hcomp.nu T.Y).target.hom) htransport₁
  simp only [Category.assoc] at h₀ h₁
  have hreal : (R.sphere ((t+1)-(s+1)) ((t+1)-d)).hom ≫ background.recovery.realization.map z ≫
      (hcomp.nu T.Y).target.hom =
      (R.sphere ((t+1)-(s+1)) ((t+1)-d)).hom ≫ background.recovery.realization.map
        (homotopyRegrade (by omega) rfl (a ≫ F)) ≫ (hcomp.nu T.Y).target.hom := by
    exact h₀.trans ((congrArg (fun z =>
      eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+1)-(s+1)=t-s by omega)) ≫ z)
      hrawreal).trans h₁.symm)
  have hdet' := hreal ▸ hdet
  exact classical_detects_of_terminal_image T.X T.Y (s,t) (s+1,t+1)
    (positiveFirstOperationLinear T hf s t) P hP hterminal w v hwp hv e (d+1) herr _ hdet'

end
end KIP126.ProofTools.Internal.SyntheticCoverage
