module
public import KIP126.AdamsComputation.Table.Dimensions

/-! Vanishing of a sphere E₂ group from its archive dimension and coordinate
isomorphism. -/
@[expose] section
namespace KIP126.Computation.Table.Internal
open KIP126.AdamsSynthetic.Completed
noncomputable section

private theorem actual_page_zero (s t : ℕ) (ht : t ≤ 261)
    (hz : basisDimension s t = 0) (x : background.classical.sphere.Page 2 (s,t)) : x = 0 := by
  let e := Standard.coordinates s t ht
  have hn : Standard.archive.basisCount s t = 0 := (archive_dimension s t ht).trans hz
  haveI : Subsingleton (Fin (Standard.archive.basisCount s t) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  apply e.injective
  exact Subsingleton.elim _ _

end
end KIP126.Computation.Table.Internal
