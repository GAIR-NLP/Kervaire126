module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Suspension.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

def evaluationFunctor (n : ℕ) : Prespectrum.{u} ⥤ BasedSpace.{u} where
  obj X := X.level n
  map f := ⟨f.level n,f.point n⟩

end KIP126.AdamsSynthetic.Source.Prespectrum
