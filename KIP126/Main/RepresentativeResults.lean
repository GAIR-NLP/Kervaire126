module

public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Selected.SphereDetection
import all KIP126.Main.Internal.Selected.ProductDetection
import all KIP126.Main.Internal.Selected.ProductZero
import all KIP126.Main.Internal.Selected.LambdaOperations

/-! Sphere representatives whose λ⁶ equation follows from the filtration
bound and the BHS comparison. -/

@[expose] section
namespace KIP126.Main
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual nonzero permanent class U has a representative on the sphere. -/
private theorem u_choice_exists :
    ∃ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum), UChoice u := by
  exact Internal.Selected.u_choice_exists

/-- Every U representative has its lambda-three eta product in filtration 14. -/
private theorem lambda_three_eta_u_filtration_fourteen
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) :
    FiltrationAtLeast background.syntheticTower 14
      (lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u)) := by
  exact Internal.Selected.u_choice_eta_lambda_three_filtration_fourteen
    Internal.Selected.h1_u_zero u hu

/-- Lambda-six divisibility with a chosen lift. -/
private theorem lambda_three_eta_u_eq_lambda_six
    (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) (hu : UChoice u) :
    ∃ y : BiHom 125 139 (S_0_0 : SyntheticSpectrum),
      lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u) =
        lambdaMultiply 6 y := by
  let a : BiHom 125 133 (S_0_0 : SyntheticSpectrum) :=
    lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u)
  have ha : FiltrationAtLeast background.syntheticTower 14 a :=
    lambda_three_eta_u_filtration_fourteen u hu
  have h := KIP126.Literature.Standard.filtration_lambda
    .sphere 125 133 14 (by decide) (a ≫ background.nu.unitIso.inv)
  change FiltrationAtLeast background.syntheticTower 14 (a ≫ background.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 139 (background.nu.functor.obj SphereSpectrum),
      lambdaMultiply 6 b = a ≫ background.nu.unitIso.inv at h
  obtain ⟨b, hb⟩ := h.mp
    (Internal.Selected.map_filtration .sphere (.nu .sphere) background.nu.unitIso.inv a ha)
  refine ⟨b ≫ background.nu.unitIso.hom, ?_⟩
  symm
  simpa only [a, lambdaMultiply, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun z => z ≫ background.nu.unitIso.hom) hb

/-- The difference of two lambda-three eta products lies in filtration 14
at degree (125, 133). -/
private theorem lambda_three_eta_u_difference_filtration_fourteen
    (u u' : BiHom 124 134 (S_0_0 : SyntheticSpectrum))
    (hu : UChoice u) (hu' : UChoice u') :
    FiltrationAtLeast background.syntheticTower 14
      ((show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from
          lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u)) -
        (show BiHom 125 133 (S_0_0 : SyntheticSpectrum) from
          lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u'))) := by
  exact (background.syntheticTower.filtrationSubmodule (S_0_0 : SyntheticSpectrum)
    14 (125, 133)).sub_mem
      (lambda_three_eta_u_filtration_fourteen u hu)
      (lambda_three_eta_u_filtration_fourteen u' hu')

end
end KIP126.Main
