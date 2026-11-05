module

public import KIP126.AdamsSynthetic.Completed.Foundations
public import KIP126.AdamsSynthetic.AdamsBackground

/-! The specified coefficient object and cofiber choices on the completed
categories. Synthetic cofibers and their finite λ quotient system are chosen
together, so the quotient laws refer to the same cofiber maps. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
noncomputable section
set_option backward.privateInPublic true

/-- Classical cones and square completions follow from the fixed
pretriangulation; their model comparisons remain separate constructions. -/
public instance spectrumCofiber : HasFunctorialCofiber (C := Spectrum) :=
  HasFunctorialCofiber.ofPretriangulated

/-- The cofiber maps and all finite λ quotient laws belong to one choice.
The existing quotient record supplies coherence, functoriality, its finite
triangle tower, restriction agreement and naturality. -/
private structure SyntheticQuotientData where
  cofiber : HasFunctorialCofiber (C := SyntheticSpectrum)
  quotients : letI := cofiber; LambdaQuotientSystem SyntheticSpectrum

private def syntheticQuotientConstruction : SyntheticQuotientData where
  cofiber := by sorry
  quotients := by sorry

public instance syntheticCofiber : HasFunctorialCofiber (C := SyntheticSpectrum) :=
  syntheticQuotientConstruction.cofiber
public def coefficients : ModTwoCoefficients Spectrum := by sorry

end
end KIP126.AdamsSynthetic.Completed
