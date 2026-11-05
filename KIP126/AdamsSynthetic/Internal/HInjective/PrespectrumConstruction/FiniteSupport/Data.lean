module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Generators

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory

universe u

namespace BasedSpace

end BasedSpace

namespace Prespectrum

/-- The free map induced by a based map, using the actual free/evaluation adjunction. -/
noncomputable def freeMap (n : ℕ) {A B : BasedSpace.{u}} (f : A ⟶ B) :
    free n A ⟶ free n B :=
  (freeEvaluation n A (free n B)).symm
    (f ≫ freeEvaluation n B (free n B) (𝟙 _))

end Prespectrum

end KIP126.AdamsSynthetic.Source
