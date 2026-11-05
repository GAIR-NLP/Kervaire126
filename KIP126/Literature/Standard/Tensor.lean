module
import all KIP126.Literature.BocksteinOriginalSuccessor
import all KIP126.Literature.BocksteinComparisonInput
import all KIP126.Literature.BocksteinBoundaryInput
public import KIP126.AdamsSynthetic.Completed.Background
import KIP126.AdamsSynthetic.Completed.Filtration
import KIP126.AdamsSynthetic.Completed.Separation
import KIP126.AdamsSynthetic.Completed.ClassicalSupport
public import KIP126.Literature.ModelResults
import all KIP126.Literature.ModelResults
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Triangles
import all KIP126.Literature.May

public import KIP126.AdamsSynthetic.Completed.SpectrumScope
public import KIP126.Literature.Standard.ClassicalInputs
import all KIP126.Literature.Standard.ClassicalInputs
public import KIP126.Literature.Standard.AdamsComparison
import all KIP126.Literature.Standard.AdamsComparison
public import KIP126.Literature.Standard.NormalizedTriangles
import all KIP126.Literature.Standard.NormalizedTriangles
public import KIP126.Literature.Standard.FiniteLift
import all KIP126.Literature.Standard.FiniteLift
public import KIP126.Literature.Standard.RealizationLifts
import all KIP126.Literature.Standard.RealizationLifts
public import KIP126.Literature.Standard.BurklundXu
import all KIP126.Literature.Standard.BurklundXu

/-! Tensor on the fixed literature background. -/

@[expose] section
set_option autoImplicit false
noncomputable section
set_option backward.privateInPublic true
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)

private def mayContextConstruction : Route.MayContext SyntheticSpectrum where
  leftShift := by sorry
  rightShift := by sorry
  leftExact := by sorry
  rightExact := by sorry

/-- The fixed mathematical object on the project background. -/
@[implicit_reducible] public def tensorLeft_commShift :
  ∀ X : SyntheticSpectrum, (tensorLeft X).CommShift ℤ :=
  mayContextConstruction.leftShift

/-- The fixed mathematical object on the project background. -/
@[implicit_reducible] public def tensorRight_commShift :
  ∀ X : SyntheticSpectrum, (tensorRight X).CommShift ℤ :=
  mayContextConstruction.rightShift


public theorem tensorLeft_isTriangulated :
  ∀ X : SyntheticSpectrum, letI := tensorLeft_commShift X; (tensorLeft X).IsTriangulated := by
  exact mayContextConstruction.leftExact


public theorem tensorRight_isTriangulated :
  ∀ X : SyntheticSpectrum, letI := tensorRight_commShift X; (tensorRight X).IsTriangulated := by
  exact mayContextConstruction.rightExact

public def mayData : Route.MayContext SyntheticSpectrum where
  leftShift := tensorLeft_commShift
  rightShift := tensorRight_commShift
  leftExact := tensorLeft_isTriangulated
  rightExact := tensorRight_isTriangulated


public theorem may_pushpull :
  ∀ T U : HoCofiberSequence (C := SyntheticSpectrum), Nonempty (Route.MayPushpullData SyntheticSpectrum mayData T U) := by
  sorry


public theorem may_signed_boundary :
  Route.MayContext.SignedBoundary SyntheticSpectrum mayData := Route.may_signed_boundary_of_source mayData may_pushpull

end KIP126.Literature.Standard
end
