module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Pullback.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

@[simp, reassoc] theorem pullbackFst_comp {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) : pullbackFst f g ≫ f = pullbackSnd f g ≫ g :=
  (pullbackPrespectrumCone f g).condition

/-- The two actual projections detect equality of strict maps. -/
theorem pullbackHom_ext {A X Y Z : Prespectrum.{u}} {f : X ⟶ Y} {g : Z ⟶ Y}
    (a b : A ⟶ pullbackPrespectrum f g)
    (h₁ : a ≫ pullbackFst f g = b ≫ pullbackFst f g)
    (h₂ : a ≫ pullbackSnd f g = b ≫ pullbackSnd f g) : a = b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (congrArg (fun k : A ⟶ X => k.level n x) h₁)
    (congrArg (fun k : A ⟶ Z => k.level n x) h₂)

end KIP126.AdamsSynthetic.Source.Prespectrum
