module

public import KIP126.AdamsComputation.Standard
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Coordinates
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Coordinates
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Range
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Range

/-! Comparison with the Cν E₂ page in every bidegree with t ≤ 200,
including empty source bidegrees, in the prescribed source coordinates.
The comparison, residual element family, and five calibrations belong to
one interpretation. The calibrations fix the top-cell label and four
bottom-map values. -/

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

@[expose] section
namespace KIP126.Computation.NuCofiberArchive
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private abbrev ActualPage (s t : ℕ) := Standard.nuCofiberSequence.Page 2 (s,t)

/- Sphere coordinate vector shared with Table.sphereBasis. -/
private def sphereCoordinate (s t i : ℕ) : background.classical.sphere.Page 2 (s,t) :=
  if ht : t ≤ 261 then
    if hi : i < Standard.archive.basisCount s t then
      (Standard.coordinates s t ht).symm (Finsupp.single ⟨i,hi⟩ 1)
    else 0
  else 0

private abbrev Comparison := ∀ s t : ℕ, InScope s t →
  ActualPage s t ≃ₗ[ℤ] Coordinate s t

private def Calibrated (e : Comparison) : Prop :=
  (e 8 134 (by decide)).symm (basisVector 8 134 ⟨0, by decide⟩) = Standard.topCell ∧
  (e 8 134 (by decide)).symm (basisVector 8 134 ⟨4, by decide⟩) =
    Standard.bottom 8 134 (sphereCoordinate 8 134 3) ∧
  (e 8 134 (by decide)).symm (basisVector 8 134 ⟨3, by decide⟩) =
    Standard.bottom 8 134 (sphereCoordinate 8 134 2) ∧
  (e 11 136 (by decide)).symm (basisVector 11 136 ⟨3, by decide⟩) =
    Standard.bottom 11 136 (sphereCoordinate 11 136 3) ∧
  (e 14 139 (by decide)).symm (basisVector 14 139 ⟨2, by decide⟩) =
    Standard.bottom 14 139 (sphereCoordinate 14 139 1)

private abbrev OutsideFamily := ∀ s t i : ℕ, ActualPage s t

/- Interpretation of the Cν coordinates on the fixed actual E₂ page
through the specified module comparison. -/
private structure RealizationData where
  interpretation : Comparison × OutsideFamily
  calibrated : Calibrated interpretation.1

private def realizationConstruction : RealizationData where
  interpretation := by sorry
  calibrated := by sorry

private def realization : Comparison × OutsideFamily :=
  realizationConstruction.interpretation

private def comparison : Comparison := realization.1

private def outsideBasis (s t i : ℕ) : ActualPage s t := realization.2 s t i

private theorem comparison_calibrated : Calibrated comparison := by
  exact realizationConstruction.calibrated

end
end KIP126.Computation.NuCofiberArchive
