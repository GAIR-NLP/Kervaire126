module

import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory

universe u

/-- The actual levelwise constant based map of sequential prespectra. -/
def zeroHom (X Y : Prespectrum.{u}) : X ⟶ Y where
  level n := ContinuousMap.const _ (Y.level n).point
  point _ := rfl
  bond n _ t := (Y.bond_point n t).symm

end KIP126.AdamsSynthetic.Source.Prespectrum
