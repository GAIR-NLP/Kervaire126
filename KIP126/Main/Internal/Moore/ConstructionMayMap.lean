module

import all KIP126.Main.Internal.Moore.Construction
import all KIP126.Main.Internal.AlphaOne.Coherence

/-! The selected middle map in the twice-rotated Moore triangle, identified
by its actual lambda factorization and diagonal uniqueness. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.Main.Internal.AlphaOne
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

private abbrev mooreSuspendedSphere :=
  background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum)

private def mooreMaySphereIso : mooreSuspendedSphere ≅ Smn (Syn:=SyntheticSpectrum) 1 1 :=
  background.nu.suspensionIso SphereSpectrum ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso background.nu.unitIso

private theorem moore_may_middle_exponent :
    normalizedExponent background.classicalTower mooreTwiceRotatedTriangle.g = 1 := by
  change normalizedExponent background.classicalTower
    (-((shiftFunctor Spectrum (1:ℤ)).map twoMap)) = 1
  rw [normalized_exponent_neg_shift .sphere .sphere twoMap,twoMap_exponent]

private def mooreMayMiddle : mooreSuspendedSphere ⟶
    (SyntheticCategory.biShift (0,-1)).obj mooreSuspendedSphere :=
  mooreMayTriangle.mor₂ ≫
    eqToHom (congrArg (fun e : ℕ =>
      (SyntheticCategory.biShift (0,-(e:ℤ))).obj mooreSuspendedSphere)
        moore_may_middle_exponent)

private theorem moore_may_middle_factorization :
    mooreMayMiddle ≫ lambdaPow 1 mooreSuspendedSphere =
      background.nu.functor.map mooreTwiceRotatedTriangle.g := by
  have transport (e : ℕ) (he : e=1)
      (f : (SyntheticCategory.biShift (0,(e:ℤ))).obj mooreSuspendedSphere ⟶ mooreSuspendedSphere) :
      (negativeLift e f ≫ eqToHom (congrArg (fun e : ℕ =>
        (SyntheticCategory.biShift (0,-(e:ℤ))).obj mooreSuspendedSphere) he)) ≫
          lambdaPow 1 mooreSuspendedSphere =
        lambdaToPositivePow e mooreSuspendedSphere ≫ f := by
    subst e
    simpa only [eqToHom_refl,Category.comp_id] using negative_lift_factorization 1 f
  exact (transport _ moore_may_middle_exponent
    (background.normalizedMap (.shift 1 .sphere) (.shift 1 .sphere)
      mooreTwiceRotatedTriangle.g).map).trans
      (background.normalizedMap (.shift 1 .sphere) (.shift 1 .sphere)
        mooreTwiceRotatedTriangle.g).factorization

private def mooreMayNegativeH0 : mooreSuspendedSphere ⟶
    (SyntheticCategory.biShift (0,-1)).obj mooreSuspendedSphere :=
  mooreMaySphereIso.hom ≫
    (SyntheticCategory.biShift (1,1)).map
      (-(negativeLift 1 KIP126.Literature.Standard.syntheticH0)) ≫
    (shiftSwap (1,1) (0,-1) (S_0_0 : SyntheticSpectrum)).inv ≫
    (SyntheticCategory.biShift (0,-1)).map mooreMaySphereIso.inv

private theorem moore_negative_h0_factorization :
    mooreMayNegativeH0 ≫ lambdaPow 1 mooreSuspendedSphere =
      background.nu.functor.map mooreTwiceRotatedTriangle.g := by
  letI := background.nu.additive
  letI := background.exactness.shiftAdditive (1,1)
  have h0 : negativeLift 1 KIP126.Literature.Standard.syntheticH0 ≫
      lambdaPow 1 (S_0_0 : SyntheticSpectrum) = 2 • 𝟙 _ :=
    (negative_lift_factorization 1 KIP126.Literature.Standard.syntheticH0).trans
      h0_positive_factorization
  have hn := lambdaPow_naturality 1 mooreMaySphereIso.inv
  change (SyntheticCategory.biShift (0,-1)).map mooreMaySphereIso.inv ≫
      lambdaPow 1 mooreSuspendedSphere =
    lambdaPow 1 (Smn (Syn:=SyntheticSpectrum) 1 1) ≫ mooreMaySphereIso.inv at hn
  simp only [mooreMayNegativeH0,Category.assoc]
  rw [hn]
  erw [lambda_pow_shift background.quotients.coherence 1 (1,1) (S_0_0 : SyntheticSpectrum)]
  simp only [Category.assoc]
  change mooreMaySphereIso.hom ≫
    (SyntheticCategory.biShift (1,1)).map (-(negativeLift 1 KIP126.Literature.Standard.syntheticH0)) ≫
      (shiftSwap (1,1) (0,-1) (S_0_0 : SyntheticSpectrum)).inv ≫
        (shiftSwap (1,1) (0,-1) (S_0_0 : SyntheticSpectrum)).hom ≫
          (SyntheticCategory.biShift (1,1)).map (lambdaPow 1 (S_0_0 : SyntheticSpectrum)) ≫
            mooreMaySphereIso.inv = _
  rw [Iso.inv_hom_id_assoc]
  erw [←Functor.map_comp_assoc,Preadditive.neg_comp,h0]
  simp only [mooreTwiceRotatedTriangle,KIP126.AdamsComputation.Moore.twoMap,
    Functor.map_neg,two_smul,Functor.map_add,
    Preadditive.comp_neg,Preadditive.neg_comp,Preadditive.comp_add,Preadditive.add_comp]
  erw [(SyntheticCategory.biShift (1,1)).map_id,
    (shiftFunctor Spectrum (1:ℤ)).map_id,background.nu.functor.map_id,
    Category.id_comp,Iso.hom_inv_id]
  rfl

/-- Uniqueness in the specified diagonal homotopy group,
from first-quotient vanishing. -/
private theorem moore_may_middle_eq_negative_h0 : mooreMayMiddle = mooreMayNegativeH0 := by
  let a := mooreMayMiddle - mooreMayNegativeH0
  have ha : a ≫ lambdaPow 1 mooreSuspendedSphere = 0 := by
    dsimp only [a]
    rw [Preadditive.sub_comp,moore_may_middle_factorization,moore_negative_h0_factorization,sub_self]
  have hz : mooreMaySphereIso.inv ≫ a = 0 :=
    lambda_one_injective_at_diagonal (.shift 1 .sphere) 1 1 (by decide)
      (mooreMaySphereIso.inv ≫ a) (by
        rw [←lambdaPow_one background.quotients.coherence]
        change (mooreMaySphereIso.inv ≫ a) ≫ lambdaPow 1 mooreSuspendedSphere = 0
        rw [Category.assoc,ha,comp_zero])
  have ha0 : a=0 := (cancel_epi mooreMaySphereIso.inv).mp (by simpa only [comp_zero] using hz)
  exact sub_eq_zero.mp ha0

private theorem moore_shifted_negative_lift
    (f : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) :
    (SyntheticCategory.biShift (1,1)).map (negativeLift 1 f) ≫
      (SyntheticCategory.biShift_comp (0,-1) (1,1)).hom.app (S_0_0 : SyntheticSpectrum) =
    (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (1,0)).map f := by
  have hi : (SyntheticCategory.biShift (1,1)).map
      (SyntheticCategory.biShift_zero.inv.app (S_0_0 : SyntheticSpectrum)) =
      (SyntheticCategory.biShift_comp (0,0) (1,1)).inv.app (S_0_0 : SyntheticSpectrum) := by
    apply (cancel_mono ((SyntheticCategory.biShift_comp (0,0) (1,1)).hom.app
      (S_0_0 : SyntheticSpectrum))).mp
    have hu := background.quotients.coherence.left_unit (1,1) (S_0_0 : SyntheticSpectrum)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,
      eqToHom_refl,Category.comp_id] at hu
    rw [Iso.inv_hom_id_app]
    erw [hu,←Functor.map_comp,Iso.inv_hom_id_app,(SyntheticCategory.biShift (1,1)).map_id]
    rfl
  have hassoc := Selected.shift_assoc_inv background.quotients.coherence
    (0,1) (0,-1) (1,1) (0,0) (1,0) (1,1)
    (by decide) (by decide) (by decide) (by decide) (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_inv,eqToIso.inv,
    eqToHom_refl,Category.id_comp] at hassoc
  simp only [negativeLift,Functor.map_comp,eqToHom_refl,Category.id_comp,
    Category.assoc]
  erw [hi,←Category.assoc,hassoc]
  simp only [Category.assoc]
  erw [(SyntheticCategory.biShift_comp (0,-1) (1,1)).hom.naturality f]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

private theorem moore_may_middle_sphere_coordinates :
    mooreMayMiddle ≫ (SyntheticCategory.biShift (0,-1)).map mooreMaySphereIso.hom ≫
      (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (S_0_0 : SyntheticSpectrum) =
    mooreMaySphereIso.hom ≫
      (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift (1,0)).map (-KIP126.Literature.Standard.syntheticH0) := by
  letI := background.exactness.shiftAdditive (0,-1)
  have hn : -(negativeLift 1 KIP126.Literature.Standard.syntheticH0) =
      negativeLift 1 (-KIP126.Literature.Standard.syntheticH0) := by
    simp only [negativeLift,Functor.map_neg,Preadditive.comp_neg]
  rw [moore_may_middle_eq_negative_h0]
  simp only [mooreMayNegativeH0,Category.assoc]
  rw [←Functor.map_comp_assoc,Iso.inv_hom_id]
  erw [(SyntheticCategory.biShift (0,-1)).map_id,Category.id_comp]
  have hswap : (shiftSwap (1,1) (0,-1) (S_0_0 : SyntheticSpectrum)).inv ≫
      (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (S_0_0 : SyntheticSpectrum) =
      (SyntheticCategory.biShift_comp (0,-1) (1,1)).hom.app (S_0_0 : SyntheticSpectrum) := by
    simp only [shiftSwap,biShiftAddIso,Iso.trans_inv,Iso.trans_hom,Iso.symm_inv,Iso.app_inv,Iso.app_hom,
      eqToIso.hom,eqToIso.inv,eqToHom_refl,
      Category.id_comp,Category.comp_id,Category.assoc,Iso.inv_hom_id_app]
  rw [hswap,hn]
  erw [moore_shifted_negative_lift]


end
end KIP126.Main.Internal.Moore
