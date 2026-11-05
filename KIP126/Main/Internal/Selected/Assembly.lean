module
import all KIP126.Main.ClassicalReduction
import all KIP126.Main.ChoiceIndependence
import all KIP126.Main.Internal.Selected.ThetaFrames
import all KIP126.Main.Internal.Selected.TargetFrame
import all KIP126.Main.Internal.Selected.ProductZero

/-! The dichotomy and both implications of Proposition 7.8,
using the specified high-filtration detector. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.Literature.Standard (eta syntheticTheta5)
open KIP126.Computation.Standard (T)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private abbrev bxEtaSquare : BiHom 125 130 (S_0_0 : SyntheticSpectrum) :=
  sphereProduct eta (sphereProduct syntheticTheta5 syntheticTheta5)

private theorem permanent_of_filtration_fifteen
    (hzero : FiltrationAtLeast background.syntheticTower 15 bxEtaSquare → bxEtaSquare=0)
    (hf : FiltrationAtLeast background.syntheticTower 15 bxEtaSquare) : H6SquarePermanent := by
  apply KIP126.Literature.Standard.h6_square_permanent_iff_lambda_eta_theta_square_eq_zero.mpr
  change lambdaMultiply 1 bxEtaSquare=0
  rw [hzero hf]
  simp only [lambdaMultiply,comp_zero]

private theorem selected_dichotomy
    (hzero : FiltrationAtLeast background.syntheticTower 15 bxEtaSquare → bxEtaSquare=0) :
    H6SquarePermanent ∨ H6SquareSupportsD12 := by
  have hf14 : FiltrationAtLeast background.syntheticTower 14 bxEtaSquare := by
    rcases theta_three_cases syntheticTheta5 with h4|hbranch
    · exact theta5_square_eta_filtration_fourteen h1_u_zero syntheticTheta5 h4
    · exact background.syntheticTower.filtrationSubmodule_antitone _ (125,130) (by decide : (14:ℤ)≤15)
        (eta_weight128_branches_filtration_fifteen (sphereProduct syntheticTheta5 syntheticTheta5) hbranch)
  by_cases hf15 : FiltrationAtLeast background.syntheticTower 15 bxEtaSquare
  · exact Or.inl (permanent_of_filtration_fifteen hzero hf15)
  · exact Or.inr (h6_square_d12_of_eta_theta_square_vanishes_mod_lambda_nine_not_ten target_page_twelve_frame
      ((lambda_9_iff_filtration_14 bxEtaSquare).mpr hf14)
      (fun h => hf15 ((lambda_10_iff_filtration_15 bxEtaSquare).mp h)))

private theorem selected_forward
    (hzero : FiltrationAtLeast background.syntheticTower 15 bxEtaSquare → bxEtaSquare=0)
    (hd : H6SquareSupportsD12) : Theta5SquareNonzeroDetection∧EtaExtensionDetection := by
  have impossible (hf : FiltrationAtLeast background.syntheticTower 15 bxEtaSquare) : False :=
    (d12_necessary hd).1 (permanent_of_filtration_fifteen hzero hf)
  have h4 : Theta5SquareNonzeroDetectionAt syntheticTheta5 := by
    rcases theta_three_cases syntheticTheta5 with h4|hbranch
    · exact h4
    · exact False.elim (impossible
        (eta_weight128_branches_filtration_fifteen (sphereProduct syntheticTheta5 syntheticTheta5) hbranch))
  refine ⟨⟨syntheticTheta5,KIP126.Literature.Standard.syntheticTheta5_detected,h4⟩,?_⟩
  obtain ⟨u,hu⟩ := u_choice_exists
  let c : BiHom 125 133 (S_0_0 : SyntheticSpectrum) := lambdaMultiply 3 (sphereProduct eta u)
  have hc14 : FiltrationAtLeast background.syntheticTower 14 c :=
    u_choice_eta_lambda_three_filtration_fourteen h1_u_zero u hu
  have hframe := target_infinity_frame KIP126.Main.SectionSeven.Internal.target_page_six_frame
  rcases theta_detection_step (14,139,133) (background.comparison.sphereE2 14 139 6 T)
      hframe c hc14 with hdet|hc15
  · exact ⟨u,hu,hdet.1⟩
  · exfalso
    apply impossible
    have hf13 := theta_sphere_frame 13 137 9 (by decide) (by decide) _ correction_infinity_generated
    have he := theta_u_eta_filtration_error hf13 syntheticTheta5 h4 u hu
    have hl := lambda_three_preserves_filtration_fifteen c hc15
    change bxEtaSquare-(show BiHom 125 130 (S_0_0 : SyntheticSpectrum) from lambdaMultiply 3 c)∈
      background.syntheticTower.filtrationSubmodule (S_0_0 : SyntheticSpectrum) 15 (125,130) at he
    have hh := (background.syntheticTower.filtrationSubmodule (S_0_0 : SyntheticSpectrum) 15 (125,130)).add_mem he hl
    simpa only [sub_add_cancel,FiltrationAtLeast,Int.reduceAdd] using hh

private theorem selected_reverse (hc3 : Stem126D6Vanishes) (hc4 : Theta5SquareNonzeroDetection) (hc5 : EtaExtensionDetection) : H6SquareSupportsD12 := by
  obtain ⟨theta,htheta,h4⟩ := hc4
  obtain ⟨u,hu,h5⟩ := hc5
  have h4' := theta5_square_nonzero_detection_choice_invariant syntheticTheta5 theta KIP126.Literature.Standard.syntheticTheta5_detected htheta h4
  have hf13 := theta_sphere_frame 13 137 9 (by decide) (by decide) _ correction_infinity_generated
  have hdetect := theta5_square_eta_extension_target_detected hf13 syntheticTheta5 h4' u hu h5
  have hn := target_detected_not_filtration_fifteen T (d6_vanishes_iff_target_survives_twelve.mp hc3) _ hdetect
  exact h6_square_d12_of_eta_theta_square_vanishes_mod_lambda_nine_not_ten target_page_twelve_frame
    ((lambda_9_iff_filtration_14 bxEtaSquare).mpr (theta5_square_eta_filtration_fourteen h1_u_zero syntheticTheta5 h4'))
    (fun h => hn ((lambda_10_iff_filtration_15 bxEtaSquare).mp h))

end
end KIP126.Main.Internal.Selected
