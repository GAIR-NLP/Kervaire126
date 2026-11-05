module
public import KIP126.Main.Conditions
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.ChoiceIndependence.Gap
import all KIP126.Main.Internal.ChoiceIndependence.Filtration

/-! Choice invariance of Theta5SquareNonzeroDetection on the fixed system. -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open KIP126.Core.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem theta5_square_nonzero_detection_invariance_of_pages
    (hpages : Subsingleton (background.classical.sphere.Page 3 (3,65)) ∧
      Subsingleton (background.classical.sphere.Page 3 (4,66)) ∧
      Subsingleton (background.classical.sphere.Page 4 (5,67)))
    (θ θ' : BiHom 62 64 (S_0_0 : SyntheticSpectrum))
    (hθ : ThetaChoice θ) (hθ' : ThetaChoice θ')
    (hc : Theta5SquareNonzeroDetectionAt θ') : Theta5SquareNonzeroDetectionAt θ := by
  classical
  let θ₀ := KIP126.Literature.Standard.syntheticTheta5
  have hbase (x : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) (hx : ThetaChoice x) :
      FiltrationAtLeast background.syntheticTower 12
        (sphereProduct x x-sphereProduct θ₀ θ₀) := by
    have hd := theta_choice_filtration_gap_of_pages hpages x θ₀ hx
      KIP126.Literature.Standard.syntheticTheta5_detected
    rw [theta_square_difference x θ₀ KIP126.Literature.Standard.syntheticTheta5_add_self]
    exact KIP126.Literature.Standard.action_filtration .sphere 62 64 62 64 6 6
      (x-θ₀) (x-θ₀) hd hd
  have hsq : FiltrationAtLeast background.syntheticTower 12
      (sphereProduct θ θ-sphereProduct θ' θ') := by
    have hsub := (background.syntheticTower.filtrationSubmodule
      (S_0_0 : SyntheticSpectrum) 12 (124,128)).sub_mem (hbase θ hθ) (hbase θ' hθ')
    have hcancel : (sphereProduct θ θ-sphereProduct θ₀ θ₀) -
        (sphereProduct θ' θ'-sphereProduct θ₀ θ₀) =
        sphereProduct θ θ-sphereProduct θ' θ' := by abel
    rw [hcancel] at hsub
    exact hsub
  refine ⟨?_,hc.2⟩
  apply detects_of_difference_in_next_filtration (background.convergence .sphere) (10,134,128) hc.1
  exact background.syntheticTower.filtrationSubmodule_antitone
    (S_0_0 : SyntheticSpectrum) (124,128) (by decide : (11:ℤ)≤12) hsq

end
end KIP126.Main.Internal.Choice
end
