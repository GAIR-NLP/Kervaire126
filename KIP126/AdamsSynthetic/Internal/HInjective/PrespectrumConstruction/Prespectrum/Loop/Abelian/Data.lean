module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Loop.Abelian.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

universe u

/-- The original cubical loop-degree equivalence as an additive equivalence. -/
def stableLoopHomotopyAddEquiv (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy (Prespectrum.loop X) d ≃+ StableHomotopy X (d+1) where
  toEquiv := stableLoopHomotopyEquiv X d
  map_add' := stableLoopHomotopyMap_add X d

end KIP126.AdamsSynthetic.Source.Prespectrum
