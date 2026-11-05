module

import all KIP126.Main.ClassicalReduction
public import KIP126.Main.ChoiceIndependence
public import KIP126.ProofTools
import all KIP126.Main.Internal.Selected.Assembly
import all KIP126.Main.Internal.High125.Injectivity

/-! Proposition 7.8 on the fixed sphere, using the finite-frame, detection,
tmf and lambda arguments. -/

@[expose] section
namespace KIP126.Main

/-- The three theta-square branches and the filtration-15 tmf detector argument. -/
private theorem permanence_or_d12 : H6SquarePermanent ∨ H6SquareSupportsD12 := by
  exact Internal.Selected.selected_dichotomy (fun hf =>
    Internal.High125.detector_injective_filtration15 _ hf
      (Internal.High125.eta_product_order_two 124 128
        (KIP126.Synthetic.Context.sphereProduct
          KIP126.Literature.Standard.syntheticTheta5 KIP126.Literature.Standard.syntheticTheta5))
      (Internal.High125.synthetic_eta_theta_square_detector_zero KIP126.Literature.Standard.syntheticTheta5))

/-- The square and eta-detection conclusions in the nonpermanent branch. -/
private theorem d12_implies_square_and_eta (hd : H6SquareSupportsD12) : Theta5SquareNonzeroDetection ∧ EtaExtensionDetection := by
  exact Internal.Selected.selected_forward (fun hf =>
    Internal.High125.detector_injective_filtration15 _ hf
      (Internal.High125.eta_product_order_two 124 128
        (KIP126.Synthetic.Context.sphereProduct
          KIP126.Literature.Standard.syntheticTheta5 KIP126.Literature.Standard.syntheticTheta5))
      (Internal.High125.synthetic_eta_theta_square_detector_zero KIP126.Literature.Standard.syntheticTheta5)) hd

/-- The reverse implication uses choice invariance, the actual target
frame and its nonzero leading class. -/
private theorem conditions_imply_d12 (hc3 : Stem126D6Vanishes) (hc4 : Theta5SquareNonzeroDetection) (hc5 : EtaExtensionDetection) : H6SquareSupportsD12 := by
  exact Internal.Selected.selected_reverse hc3 hc4 hc5

/-- LWX Proposition 7.8: both the exclusive dichotomy and the full criterion. -/
public theorem h6_square_differential_dichotomy_and_criterion :
    ((H6SquarePermanent ∧ ¬ H6SquareSupportsD12) ∨ (H6SquareSupportsD12 ∧ ¬ H6SquarePermanent)) ∧
      (H6SquareSupportsD12 ↔ Stem126D6Vanishes ∧ Theta5SquareNonzeroDetection ∧ EtaExtensionDetection) := by
  constructor
  · rcases permanence_or_d12 with hp | hd
    · exact Or.inl ⟨hp, fun hd => (d12_necessary hd).1 hp⟩
    · exact Or.inr ⟨hd, (d12_necessary hd).1⟩
  · constructor
    · intro hd
      exact ⟨(d12_necessary hd).2, d12_implies_square_and_eta hd⟩
    · rintro ⟨h3, h4, h5⟩
      exact conditions_imply_d12 h3 h4 h5

end KIP126.Main
