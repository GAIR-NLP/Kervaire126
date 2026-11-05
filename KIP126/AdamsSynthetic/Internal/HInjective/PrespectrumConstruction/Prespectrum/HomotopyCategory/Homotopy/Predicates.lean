module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyCategory.Homotopy.Data
import Mathlib.CategoryTheory.Quotient

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory
universe u

/-- Two strict maps are related exactly when an actual strict based path
homotopy exists between them. -/
def pathHomotopic : HomRel Prespectrum.{u} := fun _ _ f g => Nonempty (StrictHomotopy f g)

end KIP126.AdamsSynthetic.Source.Prespectrum
