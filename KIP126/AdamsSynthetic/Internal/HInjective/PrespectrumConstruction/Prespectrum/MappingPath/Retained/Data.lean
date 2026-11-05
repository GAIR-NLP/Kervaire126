module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingPath.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyCategory.Homotopy.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory
universe u

/-- Retain the actual path in the mapping-path total space as a strict
map to the path prespectrum. -/
def mappingPathRetainedPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPath f ⟶ pathPrespectrum Y where
  level n := ⟨fun z => z.val.2,continuous_subtype_val.snd⟩
  point _ := rfl
  bond _ _ _ := rfl

/-- The retained path is a genuine strict homotopy from the source map
to the endpoint projection of its actual mapping-path factorization. -/
def mappingPathRetainedHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    StrictHomotopy (mappingPathRetraction f ≫ f) (mappingPathProjection f) where
  hom := mappingPathRetainedPath f
  zero := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    exact z.property
  one := rfl

end KIP126.AdamsSynthetic.Source.Prespectrum
