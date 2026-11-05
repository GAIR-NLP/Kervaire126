module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.Topology.HomotopyLifting.Cube.Boundary.Proofs
import Mathlib.CategoryTheory.LiftingProperties.Basic

@[expose] section

namespace KIP126.Topology.HomotopyLifting

open CategoryTheory Set _root_.Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The full boundary of a finite cube is closed, including the empty
boundary of the zero-dimensional cube. -/
theorem cubeBoundary_isClosed (n : ℕ) :
    IsClosed (_root_.Cube.boundary (Fin n)) := by
  simpa only [_root_.Cube.boundary,Set.setOf_exists,Set.setOf_or] using
    isClosed_iUnion_of_finite (fun i : Fin n =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const))

instance cubeBoundaryObject_compactSpace (n : ℕ) : CompactSpace (cubeBoundaryObject.{u} n) := by
  letI : CompactSpace (↥(_root_.Cube.boundary (Fin n))) :=
    isCompact_iff_compactSpace.mp (cubeBoundary_isClosed n).isCompact
  exact inferInstanceAs (CompactSpace (ULift.{u} (↥(_root_.Cube.boundary (Fin n)))))

/-- The specified full boundary map is an actual closed embedding. -/
theorem cubeBoundaryInclusion_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (cubeBoundaryInclusion.{u} n) := by
  change IsClosedEmbedding (fun x : ULift.{u} (↥(_root_.Cube.boundary (Fin n))) =>
    ULift.up x.down.val)
  exact Homeomorph.ulift.symm.isClosedEmbedding.comp
    ((cubeBoundary_isClosed n).isClosedEmbedding_subtypeVal.comp
      Homeomorph.ulift.isClosedEmbedding)

end KIP126.Topology.HomotopyLifting
