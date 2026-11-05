module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Path.Map.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory
open scoped unitInterval

universe u

@[simp, reassoc] theorem pathMap_evaluation {X Y : Prespectrum.{u}} (f : X ⟶ Y) (s : I) :
    pathMap f ≫ pathEvaluation Y s = pathEvaluation X s ≫ f := rfl

end KIP126.AdamsSynthetic.Source.Prespectrum
