module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Pullback.Path.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory
open scoped unitInterval

universe u

@[simp, reassoc] theorem pullbackPathLift_fst {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (H : A ⟶ pathPrespectrum X) (K : A ⟶ pathPrespectrum Z)
    (h : ∀ s : I, H ≫ pathEvaluation X s ≫ f = K ≫ pathEvaluation Z s ≫ g) (s : I) :
    pullbackPathLift H K h ≫ pathEvaluation (pullbackPrespectrum f g) s ≫ pullbackFst f g =
      H ≫ pathEvaluation X s := rfl

@[simp, reassoc] theorem pullbackPathLift_snd {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (H : A ⟶ pathPrespectrum X) (K : A ⟶ pathPrespectrum Z)
    (h : ∀ s : I, H ≫ pathEvaluation X s ≫ f = K ≫ pathEvaluation Z s ≫ g) (s : I) :
    pullbackPathLift H K h ≫ pathEvaluation (pullbackPrespectrum f g) s ≫ pullbackSnd f g =
      K ≫ pathEvaluation Z s := rfl

end KIP126.AdamsSynthetic.Source.Prespectrum
