module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.BasedSpace.Colimit.Instances
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Tail.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The actual based colimit at each level of any small strict diagram. -/
noncomputable def pointwiseColimitLevel {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) : BasedSpace.{u} :=
  colimit (F ⋙ evaluationFunctor n)

noncomputable def pointwiseColimitLevelInclusion {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) (j : J) :
    (F.obj j).level n ⟶ pointwiseColimitLevel F n :=
  colimit.ι (F ⋙ evaluationFunctor n) j

end KIP126.AdamsSynthetic.Source.Prespectrum
