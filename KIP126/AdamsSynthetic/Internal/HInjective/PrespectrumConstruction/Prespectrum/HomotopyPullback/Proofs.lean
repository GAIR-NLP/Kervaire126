module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyPullback.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Pullback.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Path.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory

universe u

@[simp] theorem homotopyPullbackPath_zero {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    homotopyPullbackPath f g ≫ pathEvaluation Y 0 = homotopyPullbackFst f g ≫ f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  exact p.val.1.property

@[simp] theorem homotopyPullbackPath_one {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    homotopyPullbackPath f g ≫ pathEvaluation Y 1 = homotopyPullbackSnd f g ≫ g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  exact p.property

@[simp, reassoc] theorem homotopyPullbackLift_fst {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (a : A ⟶ X) (b : A ⟶ Z)
    (H : A ⟶ pathPrespectrum Y) (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f)
    (h₁ : H ≫ pathEvaluation Y 1 = b ≫ g) :
    homotopyPullbackLift a b H h₀ h₁ ≫ homotopyPullbackFst f g = a := rfl

@[simp, reassoc] theorem homotopyPullbackLift_snd {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (a : A ⟶ X) (b : A ⟶ Z)
    (H : A ⟶ pathPrespectrum Y) (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f)
    (h₁ : H ≫ pathEvaluation Y 1 = b ≫ g) :
    homotopyPullbackLift a b H h₀ h₁ ≫ homotopyPullbackSnd f g = b := rfl

/-- The actual retained homotopy makes the original square commute after
ordinary stable localization. -/
theorem source_homotopyPullback_comm {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    sourceLocalization.map (homotopyPullbackFst f g) ≫ sourceLocalization.map f =
      sourceLocalization.map (homotopyPullbackSnd f g) ≫ sourceLocalization.map g := by
  rw [← CategoryTheory.Functor.map_comp, ← homotopyPullbackPath_zero,
    CategoryTheory.Functor.map_comp, source_pathEvaluation_eq Y 0 1,
    ← CategoryTheory.Functor.map_comp, homotopyPullbackPath_one,
    CategoryTheory.Functor.map_comp]

end KIP126.AdamsSynthetic.Source.Prespectrum
