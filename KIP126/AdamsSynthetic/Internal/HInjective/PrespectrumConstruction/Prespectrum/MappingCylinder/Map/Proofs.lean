module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingCylinder.Map.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem mappingCylinderInclusion_natural {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    mappingCylinderInclusion f ≫ mappingCylinderMap f g a b h =
      a ≫ mappingCylinderInclusion g := rfl

end KIP126.AdamsSynthetic.Source.Prespectrum
