module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Replacement.Cubical.Lifting.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u

/-- Actual left lifting against every strict map with full cube-boundary
lifting on each of its original topological levels. -/
def IsCubicallyCofibrant (X : Prespectrum.{u}) : Prop :=
  ∀ {E B : Prespectrum.{u}} (p : E ⟶ B),
    (∀ n,HasCubeBoundaryLifting (p.level n)) →
      HasLiftingProperty (zeroMap zeroPrespectrum X) p

end KIP126.AdamsSynthetic.Source.Prespectrum
