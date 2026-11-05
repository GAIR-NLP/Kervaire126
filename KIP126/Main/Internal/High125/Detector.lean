module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.ChoiceIndependence.LambdaInjectivity
import all KIP126.Main.Internal.ChoiceIndependence.OrderTwo
import all KIP126.Main.Internal.High125.Pages
/-! The tmf injectivity and Hurewicz argument. Vanishing in stem 62
gives the realization conclusion for every sphere representative. -/
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum Spectrum)
open KIP126.Main.Internal.Choice
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def detectorMap : (S_0_0 : SyntheticSpectrum) ⟶ background.nu.functor.obj background.auxiliary.detector :=
  background.nu.unitIso.inv ≫ background.nu.functor.map background.auxiliary.detectorUnit

private theorem detector_page_two_zero (s : ℤ) (hs : s ≤ 0) :
    Subsingleton ((background.classical.obj background.auxiliary.detector).Page 2 (s,63+s)) := by
  let f := (background.classical.map Standard.tmfIso.hom).pageMap 2 (s,63+s)
  let g := (background.classical.map Standard.tmfIso.inv).pageMap 2 (s,63+s)
  have hgf : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.pageMap_comp,←ClassicalAdamsFamily.map_comp,
      Iso.inv_hom_id,ClassicalAdamsFamily.map_id,SpectralSequenceMorphism.pageMap_id]
  have hf (a : (background.classical.obj background.auxiliary.detector).Page 2 (s,63+s)) : f (g a)=a :=
    ConcreteCategory.congr_hom hgf a
  letI := Standard.tmf_low_filtration63 s hs
  exact ⟨fun a b => (hf a).symm.trans ((congrArg f (Subsingleton.elim (g a) (g b))).trans (hf b))⟩

theorem detector_realization_injective_62_64 :
    Function.Injective (fun a : BiHom 62 64 (background.nu.functor.obj background.auxiliary.detector) =>
      background.recovery.realization.map a) := by
  apply realization_injective_of_lambda_powers (.nu .detector) 62 64
  apply nu_lambda_powers_injective_of_source_halfplane .detector 62 64
  intro q hq r hr x
  have he := page_subsingleton_of_le (background.classical.obj background.auxiliary.detector)
    2 r q (63+q) (by decide) hr (detector_page_two_zero q (by omega))
  have hz : Subsingleton ((background.classical.obj background.auxiliary.detector).Page r (q,q+62+1)) := by
    simpa only [show q+62+1=63+q by omega] using he
  rw [hz.elim x 0,map_zero]

theorem synthetic_theta_detector_zero
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    theta ≫ detectorMap = 0 := by
  letI := realization_additive
  let a := theta ≫ detectorMap
  let alpha : HomotopyGroup (C := Spectrum) 62 Standard.tmf :=
    (Standard.realization_sphere 62 64).hom ≫ background.recovery.realization.map a ≫
      (background.recovery.nuRealizationIso.app background.auxiliary.detector).hom ≫ Standard.tmfIso.inv
  have hz := Standard.tmf_vanishing62 alpha
  apply detector_realization_injective_62_64
  dsimp only
  rw [Functor.map_zero]
  apply (cancel_epi (Standard.realization_sphere 62 64).hom).mp
  apply (cancel_mono ((background.recovery.nuRealizationIso.app background.auxiliary.detector).hom ≫
    Standard.tmfIso.inv)).mp
  simpa only [alpha,Category.assoc,comp_zero,zero_comp] using hz

theorem synthetic_eta_theta_square_detector_zero
    (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) :
    sphereProduct Standard.eta (sphereProduct theta theta) ≫ detectorMap = 0 := by
  have h := synthetic_theta_detector_zero theta
  dsimp only [sphereProduct]
  simp only [Smn] at h
  simp only [Smn,Category.assoc]
  rw [h]
  erw [comp_zero,comp_zero,comp_zero,comp_zero]

end
end KIP126.Main.Internal.High125
