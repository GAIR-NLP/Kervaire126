module


/- Literature objects, comparison witnesses and results for one model. -/
public import KIP126.Literature.Classical
import all KIP126.Literature.Classical
public import KIP126.Literature.Rigidity
import all KIP126.Literature.Rigidity
public import KIP126.Literature.Triangles
import all KIP126.Literature.Triangles
public import KIP126.Literature.Lift
import all KIP126.Literature.Lift
public import KIP126.Literature.EInfinity
import all KIP126.Literature.EInfinity
public import KIP126.Literature.SyntheticComparison
import all KIP126.Literature.SyntheticComparison
public import KIP126.Literature.RealizationTransport
import all KIP126.Literature.RealizationTransport
public import KIP126.Literature.ClassicalRange
import all KIP126.Literature.ClassicalRange
public import KIP126.Literature.BX
import all KIP126.Literature.BX
public import KIP126.Literature.Secondary
import all KIP126.Literature.Secondary

/-!
Correlated literature objects, comparisons and results on the supplied model.
-/


@[expose] section
set_option autoImplicit false
namespace KIP126.Literature
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : AdamsSyntheticBackground C Syn)

/-- Sources, their fixed coordinates, and comparison witnesses. -/
private structure LiteratureBindings extends ClassicalBindings D where
  rigidity : RigidityBindings D
  eInfinity : EInfinityPresentation D
  infinityShift : InfinityShiftCoordinates D
  weights_lambda : ∀ (X : AdamsObject (coefficients := D.coefficients)) (s t w₁ w₂ : ℤ)
    (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    rigidity.weights.map X s t w₁ w₂ hw ht = infinityShift.weightMap D X s t w₁ w₂ hw
  tmfSource : TmfSourceData D tmf
  secondary : SecondaryBindings D
  nuCofiber : NuCofiberApplicability D
  realizationTransport : SelectedRealizationComparisons D realization

/-- Results for the same bindings; arbitrary-choice θ₅ transport is a
separate hypothesis. -/
private structure LiteratureResults (B : LiteratureBindings D) where
  foundation : ClassicalFoundationResults D
  classical : ClassicalResults D B.toClassicalBindings
  classicalRange : ClassicalRangeResults D
  rigidity : RigidityResults D B.rigidity
  triangles : NormalizedTriangleResults D
  lifts : LiftSourceResults D
  eInfinity : EInfinityCompatibility D B.eInfinity B.infinityShift
  syntheticComparison : SyntheticComparisonResults D
  selectedComparisons : SelectedSyntheticComparisons D
  realization : SyntheticRealizationResults D B.realization
  tmf : TmfSourceResults D B.tmfSource
  bx : BXDistinguishedInput D B.eta
  secondary : SecondaryResults D B.toClassicalBindings B.secondary

/-- Correlated bindings and results for one model. -/
private structure LiteratureInterface where
  bindings : LiteratureBindings D
  results : LiteratureResults D bindings

/-- The corrected weight map is epi by the same actual λ/quotient formula. -/
private theorem LiteratureInterface.weight_epi (L : LiteratureInterface D)
    (X : AdamsObject (coefficients := D.coefficients)) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t) :
    CategoryTheory.Epi (L.bindings.rigidity.weights.map X s t w₁ w₂ hw ht) := by
  rw [L.bindings.weights_lambda]
  exact L.results.eInfinity.weight_epi D X s t w₁ w₂ hw ht

end KIP126.Literature
