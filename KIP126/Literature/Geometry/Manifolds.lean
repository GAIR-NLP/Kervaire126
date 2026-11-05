module

import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The geometric objects in AimPaper's introduction: compact boundaryless
smooth manifolds with Hausdorff, second-countable topology and stable
tangent framings. -/

namespace KIP126.Literature.Geometry
open Bundle
open scoped Manifold ContDiff Bundle

/-- A closed smooth n-manifold, with its actual atlas and topology. -/
private structure ClosedSmoothManifoldData (n : ℕ) where
  Carrier : Type
  [topology : TopologicalSpace Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]
  [compact : CompactSpace Carrier]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin n)) Carrier]
  [smooth : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ Carrier]

attribute [instance] ClosedSmoothManifoldData.topology ClosedSmoothManifoldData.hausdorff
  ClosedSmoothManifoldData.secondCountable ClosedSmoothManifoldData.compact
  ClosedSmoothManifoldData.charted ClosedSmoothManifoldData.smooth

/-- Closed smooth manifolds. -/
public def ClosedSmoothManifold (n : ℕ) : Type 1 := ClosedSmoothManifoldData n

/-- A stable tangent framing: a smooth global frame on TM ⊕ ε^r, with r
included in the data, as in framed cobordism. -/
private structure StableFramingData {n : ℕ} (M : ClosedSmoothManifoldData n) where
  rank : ℕ
  sections : Fin (n + rank) → (x : M.Carrier) →
    ((TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) : M.Carrier → Type) ×ᵇ
      Bundle.Trivial M.Carrier (EuclideanSpace ℝ (Fin rank))) x
  isFrame : IsLocalFrameOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin rank)) ∞ sections Set.univ

/-- Smooth global frames of the stabilized tangent bundle. -/
public def StableFraming {n : ℕ} (M : ClosedSmoothManifold n) : Type :=
  StableFramingData M

/-- A closed smooth manifold with a specified stable framing. -/
private structure ClosedStablyFramedManifoldData (n : ℕ) where
  manifold : ClosedSmoothManifoldData n
  framing : StableFramingData manifold

/-- Closed smooth manifolds with specified stable tangent framings. -/
public def ClosedStablyFramedManifold (n : ℕ) : Type 1 :=
  ClosedStablyFramedManifoldData n

end KIP126.Literature.Geometry
