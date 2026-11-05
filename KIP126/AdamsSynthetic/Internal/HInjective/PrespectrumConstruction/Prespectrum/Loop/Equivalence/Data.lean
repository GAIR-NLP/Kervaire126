module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Loop.Comparison

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
universe u

/-- The actual pointwise loop prespectrum has the expected shifted stable
homotopy, with its two inverse maps defined on genuine cubical representatives. -/
def stableLoopHomotopyEquiv (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy (Prespectrum.loop X) d ≃ StableHomotopy X (d+1) where
  toFun := stableLoopHomotopyMap X d
  invFun := stableLoopHomotopyInverse X d
  left_inv := stableLoopHomotopyInverse_map X d
  right_inv := stableLoopHomotopyMap_inverse X d

end KIP126.AdamsSynthetic.Source.Prespectrum
