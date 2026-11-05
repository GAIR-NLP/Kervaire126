module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.Prespectrum.HomotopyGroup.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

universe u

/-- All the actual based cubical stabilization maps are bijective. -/
def HasBijectiveStabilization (X : Prespectrum.{u}) : Prop :=
  ∀ n r, Function.Bijective (stabilizeHomotopy X n r)

end KIP126.AdamsSynthetic.Source.Prespectrum
