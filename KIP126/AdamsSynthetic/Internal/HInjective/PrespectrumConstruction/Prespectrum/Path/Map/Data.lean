module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.Prespectrum.Path.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory
open scoped unitInterval

universe u

/-- Postcompose each retained path with a strict prespectrum map. -/
def pathMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    pathPrespectrum X ⟶ pathPrespectrum Y where
  level n := ⟨fun p => (f.level n).comp p, ContinuousMap.continuous_postcomp (f.level n)⟩
  point n := by
    apply ContinuousMap.ext
    intro s
    exact f.point n
  bond n p t := by
    change C(I, X.level n) at p
    apply ContinuousMap.ext
    intro s
    exact f.bond n (p s) t

end KIP126.AdamsSynthetic.Source.Prespectrum
