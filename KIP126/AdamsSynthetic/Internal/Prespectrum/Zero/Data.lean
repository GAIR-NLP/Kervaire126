module

import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
universe u

/-- The actual prespectrum with one point at every level. -/
def zeroPrespectrum : Prespectrum.{u} where
  level _ := { space := TopCat.of PUnit, point := PUnit.unit }
  bond _ := ContinuousMap.const _ PUnit.unit
  bond_point _ _ := rfl
  bond_zero _ _ := rfl
  bond_one _ _ := rfl

/-- The actual constant based map, level by level. -/
def zeroMap (X Y : Prespectrum.{u}) : X ⟶ Y where
  level n := ContinuousMap.const _ (Y.level n).point
  point _ := rfl
  bond n _ t := (Y.bond_point n t).symm

end KIP126.AdamsSynthetic.Source.Prespectrum
