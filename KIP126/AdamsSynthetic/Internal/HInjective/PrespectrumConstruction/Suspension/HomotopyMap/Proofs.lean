module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Suspension.HomotopyMap.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Suspension.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum.HomotopyMap

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u
variable {X Y : Prespectrum.{u}} (f : HomotopyMap X Y)

@[simp] theorem sourceSection_point (n : ℕ) :
    f.sourceSection n (X.level n).point = (f.pathLevel n).point := by
  apply Subtype.ext
  apply Prod.ext <;> try rfl
  apply ContinuousMap.ext
  intro t
  exact f.point n

end KIP126.AdamsSynthetic.Source.Prespectrum.HomotopyMap
