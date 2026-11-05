module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Fiber.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Path.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory
universe u

@[simp] theorem fiberNullPath_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberNullPath f ≫ pathEvaluation Y 0 = fiberProjection f ≫ f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact z.property.1

@[simp] theorem fiberNullPath_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberNullPath f ≫ pathEvaluation Y 1 = zeroMap _ _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact z.property.2

end KIP126.AdamsSynthetic.Source.Prespectrum
