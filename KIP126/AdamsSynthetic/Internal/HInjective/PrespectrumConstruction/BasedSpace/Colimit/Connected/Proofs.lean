module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.BasedSpace.Under.Data
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- In a connected based diagram the basepoints already have a common
image, so its based colimit is also the actual topological colimit. -/
noncomputable instance forgetToTop_preservesConnectedColimits
    (J : Type w) [Category.{v} J] [IsConnected J] :
    PreservesColimitsOfShape J forgetToTop.{u} := by
  change PreservesColimitsOfShape J (underEquivalence.functor ⋙ Under.forget pointSpace)
  infer_instance

end KIP126.AdamsSynthetic.Source.BasedSpace
